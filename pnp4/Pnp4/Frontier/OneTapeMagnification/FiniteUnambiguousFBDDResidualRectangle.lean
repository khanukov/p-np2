import Pnp4.Frontier.OneTapeMagnification.FiniteResidualAcceptedModelCount
import Pnp4.Frontier.OneTapeMagnification.UnambiguousFBDDIndicatorLocality

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact residual rectangles for finite read-once branching DAGs

A last-common-suffix argument needs one purely combinatorial fact.  At a
vertex `v`, the variables which may be queried before `v` are disjoint from
those which may be queried from `v` to acceptance.  Consequently a compatible
prefix can be spliced with an arbitrary compatible accepting suffix.

This file records that fact as an exact finite rectangle equivalence.  One
factor consists of normalized accepting suffix models on `postVars v`.  The
other consists of full inputs which have a compatible prefix to `v` and agree
with a fixed reference input on `postVars v`.  Their product is equivalent to
the set of full inputs which have both a compatible prefix and a compatible
accepting suffix at `v`.

No unambiguity, completeness, correlation estimate, or probabilistic premise
is used.  Syntactic read-once is the sole graph hypothesis.  The cardinal
corollaries are the exact splice-capacity input needed by a future
edge-labelled last-common-prefix grouping.
-/

noncomputable section

namespace FiniteUnambiguousFBDD

open FiniteResidualAcceptedModelCount

/-- Replace the coordinates in `postVars vertex` by `suffix`, retaining
`prefix` on every other coordinate. -/
def spliceAtPostVars {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (suffix outside : Fin n -> Bool) : Fin n -> Bool :=
  fun queryIndex =>
    if queryIndex ∈ B.postVars vertex then suffix queryIndex
    else outside queryIndex

@[simp]
theorem spliceAtPostVars_eq_suffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (suffix outside : Fin n -> Bool) {queryIndex : Fin n}
    (hpost : queryIndex ∈ B.postVars vertex) :
    B.spliceAtPostVars vertex suffix outside queryIndex = suffix queryIndex := by
  simp [spliceAtPostVars, hpost]

@[simp]
theorem spliceAtPostVars_eq_prefix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (suffix outside : Fin n -> Bool) {queryIndex : Fin n}
    (hpost : queryIndex ∉ B.postVars vertex) :
    B.spliceAtPostVars vertex suffix outside queryIndex = outside queryIndex := by
  simp [spliceAtPostVars, hpost]

/-- A canonical representative of one residual accepting suffix model.
Coordinates outside `postVars vertex` are normalized to `false`. -/
def ResidualSuffixModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) : Type :=
  {input : Fin n -> Bool //
    (∀ queryIndex, queryIndex ∉ B.postVars vertex -> input queryIndex = false) ∧
      B.HasCompatibleAcceptingSuffix input vertex}

/-- Prefix-side models relative to one fixed post-variable assignment.
They need not be accepted by themselves: they only need a compatible prefix
to `vertex` and the prescribed values on `postVars vertex`. -/
def FixedPostPrefixModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex) : Type :=
  {input : Fin n -> Bool //
    B.HasCompatiblePrefix input vertex ∧
      ∀ queryIndex, queryIndex ∈ B.postVars vertex ->
        input queryIndex = reference queryIndex}

/-- Full inputs whose accepting computation can be routed through `vertex`.
The prefix and suffix witnesses are kept existential, exactly as in the
finite uFBDD semantics. -/
def ThroughModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) : Type :=
  {input : Fin n -> Bool //
    B.HasCompatiblePrefix input vertex ∧
      B.HasCompatibleAcceptingSuffix input vertex}

instance residualSuffixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    Fintype (B.ResidualSuffixModel vertex) := by
  classical
  unfold ResidualSuffixModel
  infer_instance

instance fixedPostPrefixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) : Fintype (B.FixedPostPrefixModel reference vertex) := by
  classical
  unfold FixedPostPrefixModel
  infer_instance

instance throughModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    Fintype (B.ThroughModel vertex) := by
  classical
  unfold ThroughModel
  infer_instance

/-- The prefix-side factor obtained from a through-model: retain the through
input before `vertex` and install the fixed reference values after it. -/
def throughModelFixedPostPrefix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) (hreadOnce : B.IsSyntacticallyReadOnce)
    (through : B.ThroughModel vertex) :
    B.FixedPostPrefixModel reference vertex := by
  let input := B.spliceAtPostVars vertex reference through.1
  refine ⟨input, ?_, ?_⟩
  · have hdisjoint := B.preVars_disjoint_postVars hreadOnce vertex
    apply (B.hasCompatiblePrefix_iff_of_eq_on_preVars
      (input := through.1) (input' := input) vertex ?_).mp through.2.1
    intro queryIndex hpre
    have hnotPost : queryIndex ∉ B.postVars vertex := by
      exact Finset.disjoint_left.mp hdisjoint hpre
    simp [input, hnotPost]
  · intro queryIndex hpost
    simp [input, hpost]

/-- The suffix-side factor obtained from a through-model: retain the through
input on `postVars vertex` and normalize every other coordinate to `false`. -/
def throughModelResidualSuffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (through : B.ThroughModel vertex) : B.ResidualSuffixModel vertex := by
  let input := B.spliceAtPostVars vertex through.1 (fun _ => false)
  refine ⟨input, ?_, ?_⟩
  · intro queryIndex hnotPost
    simp [input, hnotPost]
  · apply (B.hasCompatibleAcceptingSuffix_iff_of_eq_on_postVars
      (input := through.1) (input' := input) vertex ?_).mp through.2.2
    intro queryIndex hpost
    simp [input, hpost]

/-- Splice a normalized accepting suffix into a compatible fixed-post prefix.
Read-once disjointness makes both compatibility witnesses survive. -/
def residualRectangleSplice {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) (hreadOnce : B.IsSyntacticallyReadOnce)
    (rectangle : B.ResidualSuffixModel vertex ×
      B.FixedPostPrefixModel reference vertex) : B.ThroughModel vertex := by
  let input := B.spliceAtPostVars vertex rectangle.1.1 rectangle.2.1
  refine ⟨input, ?_, ?_⟩
  · have hdisjoint := B.preVars_disjoint_postVars hreadOnce vertex
    apply (B.hasCompatiblePrefix_iff_of_eq_on_preVars
      (input := rectangle.2.1) (input' := input) vertex ?_).mp
        rectangle.2.2.1
    intro queryIndex hpre
    have hnotPost : queryIndex ∉ B.postVars vertex := by
      exact Finset.disjoint_left.mp hdisjoint hpre
    simp [input, hnotPost]
  · apply (B.hasCompatibleAcceptingSuffix_iff_of_eq_on_postVars
      (input := rectangle.1.1) (input' := input) vertex ?_).mp
        rectangle.1.2.2
    intro queryIndex hpost
    simp [input, hpost]

/-- Exact residual rectangle at a read-once vertex. -/
def residualRectangleEquiv {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.ResidualSuffixModel vertex ×
      B.FixedPostPrefixModel reference vertex) ≃ B.ThroughModel vertex where
  toFun := B.residualRectangleSplice reference vertex hreadOnce
  invFun := fun through =>
    ⟨B.throughModelResidualSuffix vertex through,
      B.throughModelFixedPostPrefix reference vertex hreadOnce through⟩
  left_inv := by
    intro rectangle
    apply Prod.ext
    · apply Subtype.ext
      funext queryIndex
      by_cases hpost : queryIndex ∈ B.postVars vertex
      · simp [residualRectangleSplice, throughModelResidualSuffix,
          spliceAtPostVars, hpost]
      · simpa [residualRectangleSplice, throughModelResidualSuffix,
          spliceAtPostVars, hpost] using rectangle.1.2.1 queryIndex hpost
    · apply Subtype.ext
      funext queryIndex
      by_cases hpost : queryIndex ∈ B.postVars vertex
      · simpa [residualRectangleSplice, throughModelFixedPostPrefix,
          spliceAtPostVars, hpost] using
            (rectangle.2.2.2 queryIndex hpost).symm
      · simp [residualRectangleSplice, throughModelFixedPostPrefix,
          spliceAtPostVars, hpost]
  right_inv := by
    intro through
    apply Subtype.ext
    funext queryIndex
    by_cases hpost : queryIndex ∈ B.postVars vertex <;>
      simp [residualRectangleSplice, throughModelResidualSuffix,
        throughModelFixedPostPrefix, spliceAtPostVars, hpost]

/-- A through-model is genuinely accepted: concatenate its compatible prefix
and compatible accepting suffix. -/
def throughModelToAcceptedModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    B.ThroughModel vertex -> B.AcceptedModel :=
  fun through => by
    refine ⟨through.1, ?_⟩
    rcases through.2.1 with ⟨prefixWalk, hprefix⟩
    rcases through.2.2 with ⟨suffix, hsuffix⟩
    exact Nonempty.intro
      { walk := prefixWalk.append suffix
        compatible := (Walk.compatible_append through.1 prefixWalk suffix).2
          ⟨hprefix, hsuffix⟩ }

/-- Forgetting the routing witness from a through-model is injective because
both subtypes retain the same full input. -/
theorem throughModelToAcceptedModel_injective {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex) :
    Function.Injective (B.throughModelToAcceptedModel vertex) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun accepted : B.AcceptedModel => accepted.1) heq

/-- Exact cardinality of the residual rectangle. -/
theorem card_throughModel_eq_card_residualSuffix_mul_card_fixedPostPrefix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    Fintype.card (B.ThroughModel vertex) =
      Fintype.card (B.ResidualSuffixModel vertex) *
        Fintype.card (B.FixedPostPrefixModel reference vertex) := by
  rw [← Fintype.card_congr
    (B.residualRectangleEquiv reference vertex hreadOnce)]
  simp

/-- Residual splice capacity: the prefix-fiber cardinality times the exact
number of normalized accepting suffix models cannot exceed the total number
of accepted inputs. -/
theorem card_fixedPostPrefix_mul_card_residualSuffix_le_acceptedModel
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    Fintype.card (B.FixedPostPrefixModel reference vertex) *
        Fintype.card (B.ResidualSuffixModel vertex) ≤
      Fintype.card B.AcceptedModel := by
  have hthrough : Fintype.card (B.ThroughModel vertex) ≤
      Fintype.card B.AcceptedModel :=
    Fintype.card_le_of_injective (B.throughModelToAcceptedModel vertex)
      (B.throughModelToAcceptedModel_injective vertex)
  rw [B.card_throughModel_eq_card_residualSuffix_mul_card_fixedPostPrefix
    reference vertex hreadOnce] at hthrough
  simpa [Nat.mul_comm] using hthrough

/-- Finset form used by a concrete last-common-prefix bucket.  Every member
of `fiber` need only supply a compatible prefix to `vertex` and agree with the
reference input on `postVars vertex`; the splice theorem then supplies the
capacity bound automatically. -/
theorem card_fiber_mul_card_residualSuffix_le_acceptedModel
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (fiber : Finset B.AcceptedModel)
    (hprefix : ∀ accepted ∈ fiber,
      B.HasCompatiblePrefix accepted.1 vertex)
    (hagrees : ∀ accepted ∈ fiber, ∀ queryIndex,
      queryIndex ∈ B.postVars vertex ->
        accepted.1 queryIndex = reference queryIndex) :
    fiber.card * Fintype.card (B.ResidualSuffixModel vertex) ≤
      Fintype.card B.AcceptedModel := by
  let toPrefix : {accepted // accepted ∈ fiber} ->
      B.FixedPostPrefixModel reference vertex := fun accepted =>
    ⟨accepted.1.1,
      hprefix accepted.1 accepted.2,
      hagrees accepted.1 accepted.2⟩
  have hinjective : Function.Injective toPrefix := by
    intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun model : B.FixedPostPrefixModel reference vertex => model.1) heq
  have hfiber : fiber.card ≤
      Fintype.card (B.FixedPostPrefixModel reference vertex) := by
    simpa using Fintype.card_le_of_injective toPrefix hinjective
  calc
    fiber.card * Fintype.card (B.ResidualSuffixModel vertex) ≤
        Fintype.card (B.FixedPostPrefixModel reference vertex) *
          Fintype.card (B.ResidualSuffixModel vertex) :=
      Nat.mul_le_mul_right _ hfiber
    _ ≤ Fintype.card B.AcceptedModel :=
      B.card_fixedPostPrefix_mul_card_residualSuffix_le_acceptedModel
        reference vertex hreadOnce

/-! ## Conditional residual rectangle -/

/-- Only the post-variable part of a suffix representative must agree with a
frozen affine base.  Coordinates outside `postVars vertex` are normalization
coordinates and are deliberately ignored. -/
def FrozenResidualSuffixModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (base mask : Fin n -> Bool) : Type :=
  {suffix : B.ResidualSuffixModel vertex //
    ∀ queryIndex, queryIndex ∈ B.postVars vertex ->
      mask queryIndex = false -> suffix.1 queryIndex = base queryIndex}

/-- Prefix-side rectangle elements which also satisfy the fixed affine
coordinates globally. -/
def FrozenFixedPostPrefixModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (base mask : Fin n -> Bool) : Type :=
  {outer : B.FixedPostPrefixModel reference vertex //
    FrozenCompatible outer.1 base mask}

/-- Through-models lying in the literal residual compatible-model set. -/
def FrozenThroughModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (vertex : B.Vertex) (base mask : Fin n -> Bool) : Type :=
  {through : B.ThroughModel vertex //
    FrozenCompatible through.1 base mask}

instance frozenResidualSuffixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n -> Bool) :
    Fintype (B.FrozenResidualSuffixModel vertex base mask) := by
  classical
  unfold FrozenResidualSuffixModel
  infer_instance

instance frozenFixedPostPrefixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) (base mask : Fin n -> Bool) :
    Fintype (B.FrozenFixedPostPrefixModel reference vertex base mask) := by
  classical
  unfold FrozenFixedPostPrefixModel
  infer_instance

instance frozenThroughModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n -> Bool) :
    Fintype (B.FrozenThroughModel vertex base mask) := by
  classical
  unfold FrozenThroughModel
  infer_instance

/-- A post-variable splice is frozen-compatible whenever its suffix values
are compatible on frozen post coordinates and its outside input is globally
frozen-compatible. -/
theorem frozenCompatible_spliceAtPostVars {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (suffix outside base mask : Fin n -> Bool)
    (hsuffix : ∀ queryIndex, queryIndex ∈ B.postVars vertex ->
      mask queryIndex = false -> suffix queryIndex = base queryIndex)
    (houtside : FrozenCompatible outside base mask) :
    FrozenCompatible (B.spliceAtPostVars vertex suffix outside) base mask := by
  intro queryIndex hmask
  by_cases hpost : queryIndex ∈ B.postVars vertex
  · rw [B.spliceAtPostVars_eq_suffix vertex suffix outside hpost]
    exact hsuffix queryIndex hpost hmask
  · rw [B.spliceAtPostVars_eq_prefix vertex suffix outside hpost]
    exact houtside queryIndex hmask

/-- The exact residual rectangle restricts to every fixed affine cylinder.
The reference input must explicitly belong to that cylinder; this is exactly
the premise supplied by a residual accepted-model fiber. -/
def frozenResidualRectangleEquiv {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    (vertex : B.Vertex) (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    (B.FrozenResidualSuffixModel vertex base mask ×
      B.FrozenFixedPostPrefixModel reference vertex base mask) ≃
        B.FrozenThroughModel vertex base mask := by
  let bare := B.residualRectangleEquiv reference vertex hreadOnce
  refine
    { toFun := fun rectangle => ?_
      invFun := fun through => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let through := bare (rectangle.1.1, rectangle.2.1)
    refine ⟨through, ?_⟩
    exact B.frozenCompatible_spliceAtPostVars vertex
      rectangle.1.1.1 rectangle.2.1.1 base mask
      rectangle.1.2 rectangle.2.2
  · let factors := bare.symm through.1
    refine
      ⟨⟨factors.1, ?_⟩,
        ⟨factors.2, ?_⟩⟩
    · intro queryIndex hpost hmask
      change
        (B.throughModelResidualSuffix vertex through.1).1 queryIndex =
          base queryIndex
      rw [show
        (B.throughModelResidualSuffix vertex through.1).1 queryIndex =
          through.1.1 queryIndex by
            simp [throughModelResidualSuffix, hpost]]
      exact through.2 queryIndex hmask
    · change FrozenCompatible
        (B.throughModelFixedPostPrefix reference vertex hreadOnce
          through.1).1 base mask
      exact B.frozenCompatible_spliceAtPostVars vertex reference
        through.1.1 base mask
        (fun queryIndex _hpost hmask => hreference queryIndex hmask)
        through.2
  · intro rectangle
    apply Prod.ext
    · apply Subtype.ext
      exact congrArg Prod.fst (bare.left_inv (rectangle.1.1, rectangle.2.1))
    · apply Subtype.ext
      exact congrArg Prod.snd (bare.left_inv (rectangle.1.1, rectangle.2.1))
  · intro through
    apply Subtype.ext
    exact bare.right_inv through.1

/-- A frozen through-model injects into the actual compatible accepted-model
finset for the same base and mask. -/
def frozenThroughModelToCompatibleAcceptedModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n -> Bool) :
    B.FrozenThroughModel vertex base mask ->
      {accepted : B.AcceptedModel //
        accepted ∈ B.compatibleAcceptedModels base mask} :=
  fun through =>
    ⟨B.throughModelToAcceptedModel vertex through.1,
      (B.mem_compatibleAcceptedModels base mask _).2 through.2⟩

/-- The preceding forgetful map is injective. -/
theorem frozenThroughModelToCompatibleAcceptedModel_injective {n : Nat}
    (B : FiniteUnambiguousFBDD n) (vertex : B.Vertex)
    (base mask : Fin n -> Bool) :
    Function.Injective
      (B.frozenThroughModelToCompatibleAcceptedModel vertex base mask) := by
  intro left right heq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun accepted : {accepted : B.AcceptedModel //
      accepted ∈ B.compatibleAcceptedModels base mask} => accepted.1.1) heq

/-- Exact cardinality of the residual rectangle inside one fixed affine
cylinder. -/
theorem card_frozenThroughModel_eq_card_frozenResidualSuffix_mul_card_frozenFixedPostPrefix
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    Fintype.card (B.FrozenThroughModel vertex base mask) =
      Fintype.card (B.FrozenResidualSuffixModel vertex base mask) *
        Fintype.card
          (B.FrozenFixedPostPrefixModel reference vertex base mask) := by
  rw [← Fintype.card_congr
    (B.frozenResidualRectangleEquiv reference vertex base mask
      hreadOnce hreference)]
  simp

/-- Sharp conditional splice capacity.  Its right side is the literal
residual accepted-model count, not the total number of accepted inputs. -/
theorem card_frozenFixedPostPrefix_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) (vertex : B.Vertex)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    Fintype.card
        (B.FrozenFixedPostPrefixModel reference vertex base mask) *
      Fintype.card (B.FrozenResidualSuffixModel vertex base mask) ≤
        B.residualAcceptedModelCount base mask := by
  have hthrough :
      Fintype.card (B.FrozenThroughModel vertex base mask) ≤
        Fintype.card {accepted : B.AcceptedModel //
          accepted ∈ B.compatibleAcceptedModels base mask} :=
    Fintype.card_le_of_injective
      (B.frozenThroughModelToCompatibleAcceptedModel vertex base mask)
      (B.frozenThroughModelToCompatibleAcceptedModel_injective
        vertex base mask)
  rw [B.card_frozenThroughModel_eq_card_frozenResidualSuffix_mul_card_frozenFixedPostPrefix
    reference vertex base mask hreadOnce hreference] at hthrough
  simpa [residualAcceptedModelCount, Nat.mul_comm] using hthrough

/-- Conditional Finset specialization for an actual residual LCP bucket.
Every fiber member is required explicitly to lie in the same frozen cylinder,
reach `vertex`, and share the reference post-assignment. -/
theorem card_frozenFiber_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) (vertex : B.Vertex)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask)
    (fiber : Finset B.AcceptedModel)
    (hfrozen : ∀ accepted ∈ fiber,
      accepted ∈ B.compatibleAcceptedModels base mask)
    (hprefix : ∀ accepted ∈ fiber,
      B.HasCompatiblePrefix accepted.1 vertex)
    (hagrees : ∀ accepted ∈ fiber, ∀ queryIndex,
      queryIndex ∈ B.postVars vertex ->
        accepted.1 queryIndex = reference.1 queryIndex) :
    fiber.card *
        Fintype.card (B.FrozenResidualSuffixModel vertex base mask) ≤
      B.residualAcceptedModelCount base mask := by
  let toPrefix : {accepted // accepted ∈ fiber} ->
      B.FrozenFixedPostPrefixModel reference.1 vertex base mask :=
    fun accepted =>
      ⟨⟨accepted.1.1,
          hprefix accepted.1 accepted.2,
          hagrees accepted.1 accepted.2⟩,
        (B.mem_compatibleAcceptedModels base mask accepted.1).1
          (hfrozen accepted.1 accepted.2)⟩
  have hinjective : Function.Injective toPrefix := by
    intro left right heq
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg
      (fun model : B.FrozenFixedPostPrefixModel
        reference.1 vertex base mask => model.1.1) heq
  have hfiber : fiber.card ≤ Fintype.card
      (B.FrozenFixedPostPrefixModel reference.1 vertex base mask) := by
    simpa using Fintype.card_le_of_injective toPrefix hinjective
  calc
    fiber.card *
        Fintype.card (B.FrozenResidualSuffixModel vertex base mask) ≤
      Fintype.card
          (B.FrozenFixedPostPrefixModel reference.1 vertex base mask) *
        Fintype.card (B.FrozenResidualSuffixModel vertex base mask) :=
      Nat.mul_le_mul_right _ hfiber
    _ ≤ B.residualAcceptedModelCount base mask :=
      B.card_frozenFixedPostPrefix_mul_card_frozenResidualSuffix_le_residualAcceptedModelCount
        reference.1 vertex base mask hreadOnce
          ((B.mem_compatibleAcceptedModels base mask reference).1 hreference)

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
