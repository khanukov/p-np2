import Pnp4.Frontier.OneTapeMagnification.FiniteUnambiguousFBDDResidualRectangle

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Residual rectangles for one fixed accepting suffix walk

A reverse last-common-prefix argument identifies an actual common suffix walk,
not every syntactically possible continuation from its first vertex.  Therefore
agreement on the global union `postVars vertex` is unnecessarily strong for
that application.

`Walk` records graph vertices but not a separate Boolean branch label when a
query's two children coincide.  Accordingly the final fiber theorem keeps
agreement of input values on the walk's query variables as an explicit
premise; a future labelled-LCP construction must prove that premise.

This file fixes one walk `suffixWalk : B.Walk vertex B.accept` and splices only
on `suffixWalk.queryVars`.  Syntactic read-once makes the query variables of
every start-to-`vertex` prefix disjoint from those of the fixed suffix.  The
resulting exact rectangle restricts to a fixed affine cylinder and yields a
sharp fiber-capacity bound whose right side is the literal residual accepted-
model count.

The fiber theorem requires agreement only on the variables actually queried
by `suffixWalk`.  It assumes no correlation estimate, rank gain, concentration
bound, completeness property, or unambiguity.
-/

noncomputable section

namespace FiniteUnambiguousFBDD

open FiniteResidualAcceptedModelCount

/-- Replace exactly the coordinates queried by `suffixWalk`, retaining the
outside input everywhere else. -/
def spliceAtSuffixQueryVars {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (suffix outside : Fin n -> Bool) : Fin n -> Bool :=
  fun queryIndex =>
    if queryIndex ∈ suffixWalk.queryVars then suffix queryIndex
    else outside queryIndex

@[simp]
theorem spliceAtSuffixQueryVars_eq_suffix {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (suffix outside : Fin n -> Bool)
    {queryIndex : Fin n} (hquery : queryIndex ∈ suffixWalk.queryVars) :
    B.spliceAtSuffixQueryVars suffixWalk suffix outside queryIndex =
      suffix queryIndex := by
  simp [spliceAtSuffixQueryVars, hquery]

@[simp]
theorem spliceAtSuffixQueryVars_eq_outside {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (suffix outside : Fin n -> Bool)
    {queryIndex : Fin n} (hquery : queryIndex ∉ suffixWalk.queryVars) :
    B.spliceAtSuffixQueryVars suffixWalk suffix outside queryIndex =
      outside queryIndex := by
  simp [spliceAtSuffixQueryVars, hquery]

/-- Query variables of a start-to-vertex walk are disjoint from those of one
fixed vertex-to-accept walk.  This is the exact read-once fact needed by the
path-specific splice. -/
theorem prefix_queryVars_disjoint_fixedSuffix_queryVars {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (prefixWalk : B.Walk B.start vertex)
    (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    Disjoint prefixWalk.queryVars suffixWalk.queryVars := by
  apply Finset.disjoint_left.2
  intro queryIndex hprefix hsuffix
  have hprefixTrace : queryIndex ∈ prefixWalk.queryTrace := by
    simpa [Walk.queryVars] using hprefix
  have hsuffixTrace : queryIndex ∈ suffixWalk.queryTrace := by
    simpa [Walk.queryVars] using hsuffix
  have hnodup := hreadOnce B.accept (prefixWalk.append suffixWalk)
  rw [Walk.queryTrace_append] at hnodup
  exact (List.nodup_append.mp hnodup).2.2
    queryIndex hprefixTrace queryIndex hsuffixTrace rfl

/-- A canonical representative of an assignment making the fixed suffix walk
compatible.  Coordinates outside the fixed walk's query variables are
normalized to `false`. -/
def FixedSuffixResidualModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept) : Type :=
  {input : Fin n -> Bool //
    (∀ queryIndex, queryIndex ∉ suffixWalk.queryVars ->
      input queryIndex = false) ∧
    suffixWalk.Compatible input}

/-- Prefix-side inputs relative to a fixed assignment on the variables queried
by the chosen suffix walk. -/
def FixedSuffixPrefixModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) : Type :=
  {input : Fin n -> Bool //
    B.HasCompatiblePrefix input vertex ∧
      ∀ queryIndex, queryIndex ∈ suffixWalk.queryVars ->
        input queryIndex = reference queryIndex}

/-- Inputs which have a compatible prefix to `vertex` and for which the fixed
suffix walk itself is compatible. -/
def FixedSuffixThroughModel {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept) : Type :=
  {input : Fin n -> Bool //
    B.HasCompatiblePrefix input vertex ∧ suffixWalk.Compatible input}

instance fixedSuffixResidualModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) :
    Fintype (B.FixedSuffixResidualModel suffixWalk) := by
  classical
  unfold FixedSuffixResidualModel
  infer_instance

instance fixedSuffixPrefixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept) :
    Fintype (B.FixedSuffixPrefixModel reference suffixWalk) := by
  classical
  unfold FixedSuffixPrefixModel
  infer_instance

instance fixedSuffixThroughModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) :
    Fintype (B.FixedSuffixThroughModel suffixWalk) := by
  classical
  unfold FixedSuffixThroughModel
  infer_instance

/-- Retain a through-input on the fixed suffix variables and normalize every
other coordinate. -/
def fixedSuffixThroughResidual {n : Nat} (B : FiniteUnambiguousFBDD n)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (through : B.FixedSuffixThroughModel suffixWalk) :
    B.FixedSuffixResidualModel suffixWalk := by
  let input := B.spliceAtSuffixQueryVars suffixWalk through.1 (fun _ => false)
  refine ⟨input, ?_, ?_⟩
  · intro queryIndex hnotQuery
    simp [input, hnotQuery]
  · apply (suffixWalk.compatible_iff_of_eq_on_queryVars ?_).mp through.2.2
    intro queryIndex hquery
    simp [input, hquery]

/-- Retain a through-input outside the fixed suffix variables and install the
reference assignment on the suffix variables. -/
def fixedSuffixThroughPrefix {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (through : B.FixedSuffixThroughModel suffixWalk) :
    B.FixedSuffixPrefixModel reference suffixWalk := by
  let input := B.spliceAtSuffixQueryVars suffixWalk reference through.1
  refine ⟨input, ?_, ?_⟩
  · rcases through.2.1 with ⟨prefixWalk, hprefix⟩
    refine ⟨prefixWalk, (prefixWalk.compatible_iff_of_eq_on_queryVars ?_).mp
      hprefix⟩
    intro queryIndex hquery
    have hnotSuffix : queryIndex ∉ suffixWalk.queryVars := by
      exact Finset.disjoint_left.mp
        (B.prefix_queryVars_disjoint_fixedSuffix_queryVars
          prefixWalk suffixWalk hreadOnce) hquery
    simp [input, hnotSuffix]
  · intro queryIndex hquery
    simp [input, hquery]

/-- Splice a normalized fixed-suffix assignment into a compatible prefix-side
input. -/
def fixedSuffixRectangleSplice {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : Fin n -> Bool) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (rectangle : B.FixedSuffixResidualModel suffixWalk ×
      B.FixedSuffixPrefixModel reference suffixWalk) :
    B.FixedSuffixThroughModel suffixWalk := by
  let input := B.spliceAtSuffixQueryVars suffixWalk rectangle.1.1 rectangle.2.1
  refine ⟨input, ?_, ?_⟩
  · rcases rectangle.2.2.1 with ⟨prefixWalk, hprefix⟩
    refine ⟨prefixWalk, (prefixWalk.compatible_iff_of_eq_on_queryVars ?_).mp
      hprefix⟩
    intro queryIndex hquery
    have hnotSuffix : queryIndex ∉ suffixWalk.queryVars := by
      exact Finset.disjoint_left.mp
        (B.prefix_queryVars_disjoint_fixedSuffix_queryVars
          prefixWalk suffixWalk hreadOnce) hquery
    simp [input, hnotSuffix]
  · apply (suffixWalk.compatible_iff_of_eq_on_queryVars ?_).mp
      rectangle.1.2.2
    intro queryIndex hquery
    simp [input, hquery]

/-- Exact rectangle for one fixed accepting suffix walk. -/
def fixedSuffixResidualRectangleEquiv {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (hreadOnce : B.IsSyntacticallyReadOnce) :
    (B.FixedSuffixResidualModel suffixWalk ×
      B.FixedSuffixPrefixModel reference suffixWalk) ≃
        B.FixedSuffixThroughModel suffixWalk where
  toFun := B.fixedSuffixRectangleSplice reference suffixWalk hreadOnce
  invFun := fun through =>
    ⟨B.fixedSuffixThroughResidual suffixWalk through,
      B.fixedSuffixThroughPrefix reference suffixWalk hreadOnce through⟩
  left_inv := by
    intro rectangle
    apply Prod.ext
    · apply Subtype.ext
      funext queryIndex
      by_cases hquery : queryIndex ∈ suffixWalk.queryVars
      · simp [fixedSuffixRectangleSplice, fixedSuffixThroughResidual,
          spliceAtSuffixQueryVars, hquery]
      · simpa [fixedSuffixRectangleSplice, fixedSuffixThroughResidual,
          spliceAtSuffixQueryVars, hquery] using
            rectangle.1.2.1 queryIndex hquery
    · apply Subtype.ext
      funext queryIndex
      by_cases hquery : queryIndex ∈ suffixWalk.queryVars
      · simpa [fixedSuffixRectangleSplice, fixedSuffixThroughPrefix,
          spliceAtSuffixQueryVars, hquery] using
            (rectangle.2.2.2 queryIndex hquery).symm
      · simp [fixedSuffixRectangleSplice, fixedSuffixThroughPrefix,
          spliceAtSuffixQueryVars, hquery]
  right_inv := by
    intro through
    apply Subtype.ext
    funext queryIndex
    by_cases hquery : queryIndex ∈ suffixWalk.queryVars <;>
      simp [fixedSuffixRectangleSplice, fixedSuffixThroughResidual,
        fixedSuffixThroughPrefix, spliceAtSuffixQueryVars, hquery]

/-- A fixed-suffix through-model is accepted by concatenating its compatible
prefix with the chosen compatible suffix walk. -/
def fixedSuffixThroughToAcceptedModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) :
    B.FixedSuffixThroughModel suffixWalk -> B.AcceptedModel :=
  fun through => by
    refine ⟨through.1, ?_⟩
    rcases through.2.1 with ⟨prefixWalk, hprefix⟩
    exact Nonempty.intro
      { walk := prefixWalk.append suffixWalk
        compatible := (Walk.compatible_append through.1 prefixWalk suffixWalk).2
          ⟨hprefix, through.2.2⟩ }

theorem fixedSuffixThroughToAcceptedModel_injective {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) :
    Function.Injective (B.fixedSuffixThroughToAcceptedModel suffixWalk) := by
  intro left right heq
  apply Subtype.ext
  exact congrArg (fun accepted : B.AcceptedModel => accepted.1) heq

/-! ## Restriction to one fixed affine cylinder -/

/-- Fixed-suffix assignments compatible with the frozen post-coordinates of
the current affine cylinder. -/
def FrozenFixedSuffixResidualModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) : Type :=
  {suffix : B.FixedSuffixResidualModel suffixWalk //
    ∀ queryIndex, queryIndex ∈ suffixWalk.queryVars ->
      mask queryIndex = false -> suffix.1 queryIndex = base queryIndex}

/-- Prefix-side fixed-suffix models in the same affine cylinder. -/
def FrozenFixedSuffixPrefixModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool) : Type :=
  {outer : B.FixedSuffixPrefixModel reference suffixWalk //
    FrozenCompatible outer.1 base mask}

/-- Fixed-suffix through-models in the same affine cylinder. -/
def FrozenFixedSuffixThroughModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) : Type :=
  {through : B.FixedSuffixThroughModel suffixWalk //
    FrozenCompatible through.1 base mask}

instance frozenFixedSuffixResidualModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) :
    Fintype (B.FrozenFixedSuffixResidualModel suffixWalk base mask) := by
  classical
  unfold FrozenFixedSuffixResidualModel
  infer_instance

instance frozenFixedSuffixPrefixModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool) :
    Fintype (B.FrozenFixedSuffixPrefixModel reference suffixWalk base mask) := by
  classical
  unfold FrozenFixedSuffixPrefixModel
  infer_instance

instance frozenFixedSuffixThroughModelFintype {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) :
    Fintype (B.FrozenFixedSuffixThroughModel suffixWalk base mask) := by
  classical
  unfold FrozenFixedSuffixThroughModel
  infer_instance

/-- A fixed-suffix splice is frozen-compatible when its suffix values agree
with the frozen base on the fixed suffix variables and its outside input is
globally frozen-compatible. -/
theorem frozenCompatible_spliceAtSuffixQueryVars {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept)
    (suffix outside base mask : Fin n -> Bool)
    (hsuffix : ∀ queryIndex, queryIndex ∈ suffixWalk.queryVars ->
      mask queryIndex = false -> suffix queryIndex = base queryIndex)
    (houtside : FrozenCompatible outside base mask) :
    FrozenCompatible
      (B.spliceAtSuffixQueryVars suffixWalk suffix outside) base mask := by
  intro queryIndex hmask
  by_cases hquery : queryIndex ∈ suffixWalk.queryVars
  · rw [B.spliceAtSuffixQueryVars_eq_suffix suffixWalk suffix outside hquery]
    exact hsuffix queryIndex hquery hmask
  · rw [B.spliceAtSuffixQueryVars_eq_outside suffixWalk suffix outside hquery]
    exact houtside queryIndex hmask

/-- The fixed-suffix rectangle restricts exactly to one affine cylinder. -/
def frozenFixedSuffixResidualRectangleEquiv {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    (B.FrozenFixedSuffixResidualModel suffixWalk base mask ×
      B.FrozenFixedSuffixPrefixModel reference suffixWalk base mask) ≃
        B.FrozenFixedSuffixThroughModel suffixWalk base mask := by
  let bare := B.fixedSuffixResidualRectangleEquiv reference suffixWalk hreadOnce
  refine
    { toFun := fun rectangle => ?_
      invFun := fun through => ?_
      left_inv := ?_
      right_inv := ?_ }
  · let through := bare (rectangle.1.1, rectangle.2.1)
    refine ⟨through, ?_⟩
    exact B.frozenCompatible_spliceAtSuffixQueryVars suffixWalk
      rectangle.1.1.1 rectangle.2.1.1 base mask
      rectangle.1.2 rectangle.2.2
  · let factors := bare.symm through.1
    refine ⟨⟨factors.1, ?_⟩, ⟨factors.2, ?_⟩⟩
    · intro queryIndex hquery hmask
      change
        (B.fixedSuffixThroughResidual suffixWalk through.1).1 queryIndex =
          base queryIndex
      rw [show
        (B.fixedSuffixThroughResidual suffixWalk through.1).1 queryIndex =
          through.1.1 queryIndex by
            simp [fixedSuffixThroughResidual, hquery]]
      exact through.2 queryIndex hmask
    · change FrozenCompatible
        (B.fixedSuffixThroughPrefix reference suffixWalk hreadOnce
          through.1).1 base mask
      exact B.frozenCompatible_spliceAtSuffixQueryVars suffixWalk reference
        through.1.1 base mask
        (fun queryIndex _hquery hmask => hreference queryIndex hmask)
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

/-- A frozen fixed-suffix through-model maps to a compatible accepted input in
the same affine cylinder. -/
def frozenFixedSuffixThroughToCompatibleAcceptedModel {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) :
    B.FrozenFixedSuffixThroughModel suffixWalk base mask ->
      {accepted : B.AcceptedModel //
        accepted ∈ B.compatibleAcceptedModels base mask} :=
  fun through =>
    ⟨B.fixedSuffixThroughToAcceptedModel suffixWalk through.1,
      (B.mem_compatibleAcceptedModels base mask _).2 through.2⟩

theorem frozenFixedSuffixThroughToCompatibleAcceptedModel_injective {n : Nat}
    (B : FiniteUnambiguousFBDD n) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool) :
    Function.Injective
      (B.frozenFixedSuffixThroughToCompatibleAcceptedModel
        suffixWalk base mask) := by
  intro left right heq
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg
    (fun accepted : {accepted : B.AcceptedModel //
      accepted ∈ B.compatibleAcceptedModels base mask} => accepted.1.1) heq

/-- Exact cardinality of the fixed-suffix residual rectangle in one affine
cylinder. -/
theorem card_frozenFixedSuffixThroughModel_eq_mul {n : Nat}
    (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    Fintype.card
        (B.FrozenFixedSuffixThroughModel suffixWalk base mask) =
      Fintype.card
          (B.FrozenFixedSuffixResidualModel suffixWalk base mask) *
        Fintype.card
          (B.FrozenFixedSuffixPrefixModel reference suffixWalk base mask) := by
  rw [← Fintype.card_congr
    (B.frozenFixedSuffixResidualRectangleEquiv reference suffixWalk base mask
      hreadOnce hreference)]
  simp

/-- Sharp path-specific conditional capacity. -/
theorem card_frozenFixedSuffixPrefix_mul_residual_le_residualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n) (reference : Fin n -> Bool)
    {vertex : B.Vertex} (suffixWalk : B.Walk vertex B.accept)
    (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : FrozenCompatible reference base mask) :
    Fintype.card
        (B.FrozenFixedSuffixPrefixModel reference suffixWalk base mask) *
      Fintype.card
        (B.FrozenFixedSuffixResidualModel suffixWalk base mask) ≤
      B.residualAcceptedModelCount base mask := by
  have hthrough :
      Fintype.card
          (B.FrozenFixedSuffixThroughModel suffixWalk base mask) ≤
        Fintype.card {accepted : B.AcceptedModel //
          accepted ∈ B.compatibleAcceptedModels base mask} :=
    Fintype.card_le_of_injective
      (B.frozenFixedSuffixThroughToCompatibleAcceptedModel
        suffixWalk base mask)
      (B.frozenFixedSuffixThroughToCompatibleAcceptedModel_injective
        suffixWalk base mask)
  rw [B.card_frozenFixedSuffixThroughModel_eq_mul reference suffixWalk
    base mask hreadOnce hreference] at hthrough
  simpa [residualAcceptedModelCount, Nat.mul_comm] using hthrough

/-- Conditional fiber capacity for an actual reverse-LCP common suffix walk.
Unlike the global-post-variable theorem, agreement is required only on
`suffixWalk.queryVars`. -/
theorem card_frozenFixedSuffixFiber_mul_residual_le_residualAcceptedModelCount
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (reference : B.AcceptedModel) {vertex : B.Vertex}
    (suffixWalk : B.Walk vertex B.accept) (base mask : Fin n -> Bool)
    (hreadOnce : B.IsSyntacticallyReadOnce)
    (hreference : reference ∈ B.compatibleAcceptedModels base mask)
    (fiber : Finset B.AcceptedModel)
    (hfrozen : ∀ accepted ∈ fiber,
      accepted ∈ B.compatibleAcceptedModels base mask)
    (hprefix : ∀ accepted ∈ fiber,
      B.HasCompatiblePrefix accepted.1 vertex)
    (hagrees : ∀ accepted ∈ fiber, ∀ queryIndex,
      queryIndex ∈ suffixWalk.queryVars ->
        accepted.1 queryIndex = reference.1 queryIndex) :
    fiber.card * Fintype.card
        (B.FrozenFixedSuffixResidualModel suffixWalk base mask) ≤
      B.residualAcceptedModelCount base mask := by
  let toPrefix : {accepted // accepted ∈ fiber} ->
      B.FrozenFixedSuffixPrefixModel reference.1 suffixWalk base mask :=
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
      (fun model : B.FrozenFixedSuffixPrefixModel
        reference.1 suffixWalk base mask => model.1.1) heq
  have hfiber : fiber.card ≤ Fintype.card
      (B.FrozenFixedSuffixPrefixModel reference.1 suffixWalk base mask) := by
    simpa using Fintype.card_le_of_injective toPrefix hinjective
  calc
    fiber.card * Fintype.card
        (B.FrozenFixedSuffixResidualModel suffixWalk base mask) ≤
      Fintype.card
          (B.FrozenFixedSuffixPrefixModel reference.1 suffixWalk base mask) *
        Fintype.card
          (B.FrozenFixedSuffixResidualModel suffixWalk base mask) :=
      Nat.mul_le_mul_right _ hfiber
    _ ≤ B.residualAcceptedModelCount base mask :=
      B.card_frozenFixedSuffixPrefix_mul_residual_le_residualAcceptedModelCount
        reference.1 suffixWalk base mask hreadOnce
          ((B.mem_compatibleAcceptedModels base mask reference).1 hreference)

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
