import Mathlib.Tactic

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact rational Fourier analysis on a finite Boolean cube

This file supplies the small amount of Fourier analysis needed by the finite
uFBDD cut route.  Everything is an exact finite sum in `ℚ`; in particular no
analytic probability space, asymptotics, or hidden choice of measure is used.
-/

namespace FiniteBooleanFourier

/-- The `{+1, -1}` encoding of a Boolean value. -/
def boolSign (value : Bool) : ℚ :=
  if value then -1 else 1

@[simp]
theorem boolSign_false : boolSign false = 1 := by
  simp [boolSign]

@[simp]
theorem boolSign_true : boolSign true = -1 := by
  simp [boolSign]

@[simp]
theorem boolSign_not (value : Bool) : boolSign (!value) = -boolSign value := by
  cases value <;> norm_num [boolSign]

@[simp]
theorem boolSign_square (value : Bool) : boolSign value * boolSign value = 1 := by
  cases value <;> norm_num [boolSign]

/-- The Walsh character indexed by `alpha`. -/
def character {n : Nat} (alpha : Finset (Fin n))
    (input : Fin n → Bool) : ℚ :=
  ∏ queryIndex ∈ alpha, boolSign (input queryIndex)

@[simp]
theorem character_empty {n : Nat} (input : Fin n → Bool) :
    character ∅ input = 1 := by
  simp [character]

/-- Characters turn a disjoint union of supports into a product. -/
theorem character_union_of_disjoint {n : Nat}
    {alpha beta : Finset (Fin n)} (hdisjoint : Disjoint alpha beta)
    (input : Fin n → Bool) :
    character (alpha ∪ beta) input =
      character alpha input * character beta input := by
  simpa [character] using
    (Finset.prod_union hdisjoint :
      (∏ queryIndex ∈ alpha ∪ beta, boolSign (input queryIndex)) = _)

/-- Every Boolean character is pointwise `{+1, -1}`-valued. -/
@[simp]
theorem character_square {n : Nat} (alpha : Finset (Fin n))
    (input : Fin n → Bool) :
    character alpha input * character alpha input = 1 := by
  unfold character
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro queryIndex hqueryIndex
  exact boolSign_square (input queryIndex)

/-- Flip one coordinate of a Boolean input. -/
def flipCoordinate {n : Nat} (input : Fin n → Bool)
    (coordinate queryIndex : Fin n) : Bool :=
  if queryIndex = coordinate then !(input queryIndex) else input queryIndex

@[simp]
theorem flipCoordinate_same {n : Nat} (input : Fin n → Bool)
    (coordinate : Fin n) :
    flipCoordinate input coordinate coordinate = !(input coordinate) := by
  simp [flipCoordinate]

@[simp]
theorem flipCoordinate_apply_of_ne {n : Nat} (input : Fin n → Bool)
    {coordinate queryIndex : Fin n} (hne : queryIndex ≠ coordinate) :
    flipCoordinate input coordinate queryIndex = input queryIndex := by
  simp [flipCoordinate, hne]

@[simp]
theorem flipCoordinate_flipCoordinate {n : Nat} (input : Fin n → Bool)
    (coordinate : Fin n) :
    flipCoordinate (flipCoordinate input coordinate) coordinate = input := by
  funext queryIndex
  by_cases hqueryIndex : queryIndex = coordinate
  · subst queryIndex
    simp
  · simp [flipCoordinate_apply_of_ne _ hqueryIndex]

/-- Flipping a fixed coordinate is an involutive permutation of the cube. -/
def flipEquiv {n : Nat} (coordinate : Fin n) :
    (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun input := flipCoordinate input coordinate
  invFun input := flipCoordinate input coordinate
  left_inv input := flipCoordinate_flipCoordinate input coordinate
  right_inv input := flipCoordinate_flipCoordinate input coordinate

/-- Flipping a coordinate in the support negates the character. -/
theorem character_flip_of_mem {n : Nat} {alpha : Finset (Fin n)}
    {coordinate : Fin n} (hcoordinate : coordinate ∈ alpha)
    (input : Fin n → Bool) :
    character alpha (flipCoordinate input coordinate) =
      -character alpha input := by
  have htail :
      (∏ queryIndex ∈ alpha.erase coordinate,
          boolSign (flipCoordinate input coordinate queryIndex)) =
        ∏ queryIndex ∈ alpha.erase coordinate,
          boolSign (input queryIndex) := by
    apply Finset.prod_congr rfl
    intro queryIndex hqueryIndex
    have hne : queryIndex ≠ coordinate :=
      (Finset.mem_erase.mp hqueryIndex).1
    simp [flipCoordinate_apply_of_ne _ hne]
  rw [← Finset.insert_erase hcoordinate]
  simp only [character, Finset.prod_insert, Finset.notMem_erase,
    not_false_eq_true, flipCoordinate_same, boolSign_not]
  rw [htail]
  ring

/-- Flipping a coordinate outside the support preserves the character. -/
theorem character_flip_of_not_mem {n : Nat} {alpha : Finset (Fin n)}
    {coordinate : Fin n} (hcoordinate : coordinate ∉ alpha)
    (input : Fin n → Bool) :
    character alpha (flipCoordinate input coordinate) =
      character alpha input := by
  unfold character
  apply Finset.prod_congr rfl
  intro queryIndex hqueryIndex
  have hne : queryIndex ≠ coordinate := by
    intro heq
    apply hcoordinate
    simpa [heq] using hqueryIndex
  simp [flipCoordinate_apply_of_ne _ hne]

/-- Complete flip law, convenient for rewriting under finite sums. -/
theorem character_flipCoordinate {n : Nat} (alpha : Finset (Fin n))
    (input : Fin n → Bool) (coordinate : Fin n) :
    character alpha (flipCoordinate input coordinate) =
      if coordinate ∈ alpha then -character alpha input
      else character alpha input := by
  by_cases hcoordinate : coordinate ∈ alpha
  · simp [hcoordinate, character_flip_of_mem hcoordinate]
  · simp [hcoordinate, character_flip_of_not_mem hcoordinate]

/-- Uniform Walsh coefficient, with exact rational normalization. -/
noncomputable def coefficient {n : Nat}
    (f : (Fin n → Bool) → ℚ) (alpha : Finset (Fin n)) : ℚ :=
  (∑ input : Fin n → Bool, f input * character alpha input) /
    (2 : ℚ) ^ n

/-- A function depends only on `support` if agreement there fixes its value. -/
def DependsOnlyOn {n : Nat} (support : Finset (Fin n))
    (f : (Fin n → Bool) → ℚ) : Prop :=
  ∀ ⦃input input' : Fin n → Bool⦄,
    (∀ queryIndex ∈ support, input queryIndex = input' queryIndex) →
      f input = f input'

/-- A coordinate outside a dependency set can be flipped without changing the
function. -/
theorem eq_flipCoordinate_of_dependsOnlyOn {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hlocal : DependsOnlyOn support f) {coordinate : Fin n}
    (hcoordinate : coordinate ∉ support) (input : Fin n → Bool) :
    f (flipCoordinate input coordinate) = f input := by
  symm
  apply hlocal
  intro queryIndex hqueryIndex
  have hne : queryIndex ≠ coordinate := by
    intro heq
    apply hcoordinate
    simpa [heq] using hqueryIndex
  exact (flipCoordinate_apply_of_ne input hne).symm

/-- The cube has exactly `2^n` inputs. -/
theorem cube_card (n : Nat) : Fintype.card (Fin n → Bool) = 2 ^ n := by
  simp

/-- The self-correlation of every character is exactly one. -/
theorem coefficient_character_self {n : Nat} (alpha : Finset (Fin n)) :
    coefficient (character alpha) alpha = 1 := by
  simp only [coefficient, character_square]
  simp

/-- Fourier locality: a coefficient vanishes as soon as its support contains a
coordinate outside any advertised dependency set. -/
theorem coefficient_eq_zero_of_mem_of_not_mem_of_dependsOnlyOn {n : Nat}
    {support alpha : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hlocal : DependsOnlyOn support f) {coordinate : Fin n}
    (halpha : coordinate ∈ alpha) (hsupport : coordinate ∉ support) :
    coefficient f alpha = 0 := by
  let summand : (Fin n → Bool) → ℚ := fun input =>
    f input * character alpha input
  have hsummand (input : Fin n → Bool) :
      summand (flipCoordinate input coordinate) = -summand input := by
    simp only [summand, eq_flipCoordinate_of_dependsOnlyOn hlocal hsupport input,
      character_flip_of_mem halpha]
    ring
  have hpermute :
      (∑ input : Fin n → Bool,
          summand (flipCoordinate input coordinate)) =
        ∑ input : Fin n → Bool, summand input := by
    exact (flipEquiv coordinate).sum_comp summand
  have hneg :
      (∑ input : Fin n → Bool,
          summand (flipCoordinate input coordinate)) =
        -(∑ input : Fin n → Bool, summand input) := by
    simp_rw [hsummand]
    simp
  have hsum : (∑ input : Fin n → Bool, summand input) = 0 := by
    linarith
  simp [coefficient, summand, hsum]

/-- Set-theoretic form of Fourier locality: every nonzero coefficient is
supported inside every valid dependency set. -/
theorem coefficient_eq_zero_of_not_subset_of_dependsOnlyOn {n : Nat}
    {support alpha : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hlocal : DependsOnlyOn support f) (hsubset : ¬alpha ⊆ support) :
    coefficient f alpha = 0 := by
  simp only [Finset.not_subset] at hsubset
  obtain ⟨coordinate, halpha, hsupport⟩ := hsubset
  exact coefficient_eq_zero_of_mem_of_not_mem_of_dependsOnlyOn
    hlocal halpha hsupport

/-- Equivalently, every nonzero Fourier support is contained in every valid
dependency set. -/
theorem subset_of_coefficient_ne_zero_of_dependsOnlyOn {n : Nat}
    {support alpha : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hlocal : DependsOnlyOn support f) (hnonzero : coefficient f alpha ≠ 0) :
    alpha ⊆ support := by
  by_contra hsubset
  exact hnonzero
    (coefficient_eq_zero_of_not_subset_of_dependsOnlyOn hlocal hsubset)

/-- Enlarging an advertised dependency set preserves locality. -/
theorem dependsOnlyOn_mono {n : Nat}
    {smallSupport largeSupport : Finset (Fin n)}
    {f : (Fin n → Bool) → ℚ} (hsubset : smallSupport ⊆ largeSupport)
    (hlocal : DependsOnlyOn smallSupport f) :
    DependsOnlyOn largeSupport f := by
  intro input input' hagrees
  apply hlocal
  intro queryIndex hqueryIndex
  exact hagrees queryIndex (hsubset hqueryIndex)

/-- The product of two local functions is local to the union of their
dependency sets. -/
theorem dependsOnlyOn_mul {n : Nat}
    {leftSupport rightSupport : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g) :
    DependsOnlyOn (leftSupport ∪ rightSupport) (fun input => f input * g input) := by
  intro input input' hagrees
  have hfEq : f input = f input' := by
    apply hf
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (Finset.mem_union_left rightSupport hqueryIndex)
  have hgEq : g input = g input' := by
    apply hg
    intro queryIndex hqueryIndex
    exact hagrees queryIndex (Finset.mem_union_right leftSupport hqueryIndex)
  change f input * g input = f input' * g input'
  rw [hfEq, hgEq]

/-! ## Independent local cubes

For disjoint prefix and suffix dependency sets, their assignments are
independent coordinates.  The following definitions expose that product cube
directly.  This avoids extending a local assignment by arbitrary values on
irrelevant global coordinates and is the form used by indicator products.
-/

/-- Boolean assignments to exactly the coordinates in a finite support. -/
abbrev LocalAssignment {n : Nat} (support : Finset (Fin n)) :=
  (queryIndex : ↥support) → Bool

/-- Restriction of a global input to a finite support. -/
def restrictAssignment {n : Nat} (support : Finset (Fin n))
    (input : Fin n → Bool) : LocalAssignment support :=
  fun queryIndex => input queryIndex

/-- Extend a local assignment by `false` outside its support.  The default is
irrelevant to every function satisfying `DependsOnlyOn support`. -/
def extendAssignment {n : Nat} (support : Finset (Fin n))
    (input : LocalAssignment support) : Fin n → Bool := fun queryIndex =>
  if hqueryIndex : queryIndex ∈ support then
    input ⟨queryIndex, hqueryIndex⟩
  else false

@[simp]
theorem extendAssignment_apply_of_mem {n : Nat}
    (support : Finset (Fin n)) (input : LocalAssignment support)
    {queryIndex : Fin n} (hqueryIndex : queryIndex ∈ support) :
    extendAssignment support input queryIndex =
      input ⟨queryIndex, hqueryIndex⟩ := by
  simp [extendAssignment, hqueryIndex]

@[simp]
theorem restrictAssignment_extendAssignment {n : Nat}
    (support : Finset (Fin n)) (input : LocalAssignment support) :
    restrictAssignment support (extendAssignment support input) = input := by
  funext queryIndex
  simp [restrictAssignment, extendAssignment, queryIndex.property]

/-- A local function equals its canonical restriction-extension
representation. -/
theorem eq_extend_restrict_of_dependsOnlyOn {n : Nat}
    {support : Finset (Fin n)} {f : (Fin n → Bool) → ℚ}
    (hlocal : DependsOnlyOn support f) (input : Fin n → Bool) :
    f input =
      f (extendAssignment support (restrictAssignment support input)) := by
  apply hlocal
  intro queryIndex hqueryIndex
  simp [restrictAssignment, extendAssignment, hqueryIndex]

/-- Inclusion of a finite support into the ambient coordinate type. -/
def supportEmbedding {n : Nat} (support : Finset (Fin n)) :
    ↥support ↪ Fin n where
  toFun := Subtype.val
  inj' := Subtype.val_injective

/-- Regard a local character support as a support in the ambient cube. -/
def liftLocalSupport {n : Nat} (support : Finset (Fin n))
    (alpha : Finset ↥support) : Finset (Fin n) :=
  alpha.map (supportEmbedding support)

/-- Restrict an ambient character support to local coordinates. -/
def localizeSupport {n : Nat} (support alpha : Finset (Fin n)) :
    Finset ↥support :=
  Finset.univ.filter (fun queryIndex : ↥support =>
    (queryIndex : Fin n) ∈ alpha)

/-- A Walsh character on a local assignment cube. -/
def localCharacter {n : Nat} {support : Finset (Fin n)}
    (alpha : Finset ↥support) (input : LocalAssignment support) : ℚ :=
  ∏ queryIndex ∈ alpha, boolSign (input queryIndex)

@[simp]
theorem localCharacter_empty {n : Nat} {support : Finset (Fin n)}
    (input : LocalAssignment support) :
    localCharacter ∅ input = 1 := by
  simp [localCharacter]

/-- Restriction intertwines local and ambient characters. -/
theorem character_liftLocalSupport {n : Nat}
    {support : Finset (Fin n)} (alpha : Finset ↥support)
    (input : Fin n → Bool) :
    character (liftLocalSupport support alpha) input =
      localCharacter alpha (restrictAssignment support input) := by
  simp [character, localCharacter, liftLocalSupport, restrictAssignment,
    supportEmbedding]

/-- Lifting a restricted character support recovers ambient intersection. -/
theorem liftLocalSupport_localizeSupport {n : Nat}
    (support alpha : Finset (Fin n)) :
    liftLocalSupport support (localizeSupport support alpha) =
      alpha ∩ support := by
  ext queryIndex
  simp only [liftLocalSupport, localizeSupport, Finset.mem_map,
    Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_inter]
  constructor
  · rintro ⟨localIndex, hlocalAlpha, hvalue⟩
    subst queryIndex
    exact ⟨hlocalAlpha, localIndex.property⟩
  · rintro ⟨halpha, hsupport⟩
    exact ⟨⟨queryIndex, hsupport⟩, halpha, rfl⟩

/-- Local supports lifted from disjoint ambient supports remain disjoint. -/
theorem liftLocalSupport_disjoint {n : Nat}
    {leftSupport rightSupport : Finset (Fin n)}
    (hdisjoint : Disjoint leftSupport rightSupport)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) :
    Disjoint (liftLocalSupport leftSupport alpha)
      (liftLocalSupport rightSupport beta) := by
  rw [Finset.disjoint_left]
  intro queryIndex hleft hright
  simp only [liftLocalSupport, Finset.mem_map] at hleft hright
  obtain ⟨leftIndex, hleftIndex, hleftValue⟩ := hleft
  obtain ⟨rightIndex, hrightIndex, hrightValue⟩ := hright
  have hqueryLeft : queryIndex ∈ leftSupport := by
    rw [← hleftValue]
    exact leftIndex.property
  have hqueryRight : queryIndex ∈ rightSupport := by
    rw [← hrightValue]
    exact rightIndex.property
  exact (Finset.disjoint_left.mp hdisjoint hqueryLeft) hqueryRight

/-- Merge assignments on two supports which cover the ambient coordinates.
The disjointness needed for this to be inverse to restriction is recorded in
`partitionAssignmentEquiv` below. -/
def combinePartitionAssignments {n : Nat}
    (leftSupport rightSupport : Finset (Fin n))
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (inputs : LocalAssignment leftSupport × LocalAssignment rightSupport) :
    Fin n → Bool := fun queryIndex =>
  if hleft : queryIndex ∈ leftSupport then
    inputs.1 ⟨queryIndex, hleft⟩
  else
    inputs.2 ⟨queryIndex, by
      have hunion : queryIndex ∈ leftSupport ∪ rightSupport := by
        rw [hcover]
        exact Finset.mem_univ queryIndex
      exact (Finset.mem_union.mp hunion).resolve_left hleft⟩

/-- A partition of the ambient coordinates identifies the global Boolean cube
with the product of its two local assignment cubes. -/
def partitionAssignmentEquiv {n : Nat}
    {leftSupport rightSupport : Finset (Fin n)}
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ) :
    (Fin n → Bool) ≃
      LocalAssignment leftSupport × LocalAssignment rightSupport where
  toFun input :=
    (restrictAssignment leftSupport input,
      restrictAssignment rightSupport input)
  invFun inputs :=
    combinePartitionAssignments leftSupport rightSupport hcover inputs
  left_inv input := by
    funext queryIndex
    by_cases hleft : queryIndex ∈ leftSupport
    · simp [combinePartitionAssignments, restrictAssignment, hleft]
    · simp [combinePartitionAssignments, restrictAssignment, hleft]
  right_inv inputs := by
    apply Prod.ext
    · funext queryIndex
      simp [restrictAssignment, combinePartitionAssignments,
        queryIndex.property]
    · funext queryIndex
      have hleft : (queryIndex : Fin n) ∉ leftSupport := by
        intro hleft
        exact (Finset.disjoint_left.mp hdisjoint hleft) queryIndex.property
      simp [restrictAssignment, combinePartitionAssignments, hleft]

theorem localCharacter_union_of_disjoint {n : Nat}
    {support : Finset (Fin n)} {alpha beta : Finset ↥support}
    (hdisjoint : Disjoint alpha beta) (input : LocalAssignment support) :
    localCharacter (alpha ∪ beta) input =
      localCharacter alpha input * localCharacter beta input := by
  simpa [localCharacter] using
    (Finset.prod_union hdisjoint :
      (∏ queryIndex ∈ alpha ∪ beta, boolSign (input queryIndex)) = _)

@[simp]
theorem localCharacter_square {n : Nat} {support : Finset (Fin n)}
    (alpha : Finset ↥support) (input : LocalAssignment support) :
    localCharacter alpha input * localCharacter alpha input = 1 := by
  unfold localCharacter
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_eq_one
  intro queryIndex hqueryIndex
  exact boolSign_square (input queryIndex)

/-- Exact uniform coefficient on the cube of assignments to `support`. -/
noncomputable def localCoefficient {n : Nat} (support : Finset (Fin n))
    (f : LocalAssignment support → ℚ) (alpha : Finset ↥support) : ℚ :=
  (∑ input : LocalAssignment support,
      f input * localCharacter alpha input) /
    (2 : ℚ) ^ support.card

/-- The exact coefficient of a separated product on two independent local
cubes.  When the underlying global supports are disjoint, a pair here is
precisely an assignment to their union. -/
noncomputable def separatedProductCoefficient {n : Nat}
    (leftSupport rightSupport : Finset (Fin n))
    (f : LocalAssignment leftSupport → ℚ)
    (g : LocalAssignment rightSupport → ℚ)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) : ℚ :=
  (∑ inputs : LocalAssignment leftSupport × LocalAssignment rightSupport,
      (f inputs.1 * localCharacter alpha inputs.1) *
        (g inputs.2 * localCharacter beta inputs.2)) /
    ((2 : ℚ) ^ leftSupport.card * (2 : ℚ) ^ rightSupport.card)

/-- Exact product factorization on independent local cubes.  This is the
rational finite-sum form of independence needed for prefix/suffix factors. -/
theorem separatedProductCoefficient_eq_mul_localCoefficient {n : Nat}
    (leftSupport rightSupport : Finset (Fin n))
    (f : LocalAssignment leftSupport → ℚ)
    (g : LocalAssignment rightSupport → ℚ)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) :
    separatedProductCoefficient leftSupport rightSupport f g alpha beta =
      localCoefficient leftSupport f alpha *
        localCoefficient rightSupport g beta := by
  classical
  let leftSummand : LocalAssignment leftSupport → ℚ := fun input =>
    f input * localCharacter alpha input
  let rightSummand : LocalAssignment rightSupport → ℚ := fun input =>
    g input * localCharacter beta input
  have hsum :
      (∑ inputs : LocalAssignment leftSupport × LocalAssignment rightSupport,
          leftSummand inputs.1 * rightSummand inputs.2) =
        (∑ leftInput : LocalAssignment leftSupport, leftSummand leftInput) *
          ∑ rightInput : LocalAssignment rightSupport,
            rightSummand rightInput := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul]
  have hleft : (2 : ℚ) ^ leftSupport.card ≠ 0 := by
    positivity
  have hright : (2 : ℚ) ^ rightSupport.card ≠ 0 := by
    positivity
  simp only [separatedProductCoefficient, localCoefficient]
  change
    (∑ inputs : LocalAssignment leftSupport × LocalAssignment rightSupport,
        leftSummand inputs.1 * rightSummand inputs.2) /
        ((2 : ℚ) ^ leftSupport.card * (2 : ℚ) ^ rightSupport.card) =
      ((∑ leftInput : LocalAssignment leftSupport, leftSummand leftInput) /
          (2 : ℚ) ^ leftSupport.card) *
        ((∑ rightInput : LocalAssignment rightSupport,
            rightSummand rightInput) / (2 : ℚ) ^ rightSupport.card)
  rw [hsum]
  field_simp

/-- Global-to-local factorization for a genuine partition of the Boolean
coordinates.  The global function is the product of a left-local and a
right-local function, and its coefficient at the union character is exactly
the product of the two local coefficients. -/
theorem coefficient_separatedProduct_eq_mul_localCoefficient_of_partition
    {n : Nat} {leftSupport rightSupport : Finset (Fin n)}
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (f : LocalAssignment leftSupport → ℚ)
    (g : LocalAssignment rightSupport → ℚ)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) :
    coefficient
        (fun input =>
          f (restrictAssignment leftSupport input) *
            g (restrictAssignment rightSupport input))
        (liftLocalSupport leftSupport alpha ∪
          liftLocalSupport rightSupport beta) =
      localCoefficient leftSupport f alpha *
        localCoefficient rightSupport g beta := by
  classical
  let leftSummand : LocalAssignment leftSupport → ℚ := fun input =>
    f input * localCharacter alpha input
  let rightSummand : LocalAssignment rightSupport → ℚ := fun input =>
    g input * localCharacter beta input
  have hliftDisjoint :
      Disjoint (liftLocalSupport leftSupport alpha)
        (liftLocalSupport rightSupport beta) :=
    liftLocalSupport_disjoint hdisjoint alpha beta
  have hsummand (input : Fin n → Bool) :
      (f (restrictAssignment leftSupport input) *
          g (restrictAssignment rightSupport input)) *
        character
          (liftLocalSupport leftSupport alpha ∪
            liftLocalSupport rightSupport beta) input =
      leftSummand (restrictAssignment leftSupport input) *
        rightSummand (restrictAssignment rightSupport input) := by
    rw [character_union_of_disjoint hliftDisjoint,
      character_liftLocalSupport, character_liftLocalSupport]
    dsimp only [leftSummand, rightSummand]
    ring
  have hsum :
      (∑ input : Fin n → Bool,
          (f (restrictAssignment leftSupport input) *
              g (restrictAssignment rightSupport input)) *
            character
              (liftLocalSupport leftSupport alpha ∪
                liftLocalSupport rightSupport beta) input) =
        ∑ inputs : LocalAssignment leftSupport × LocalAssignment rightSupport,
          leftSummand inputs.1 * rightSummand inputs.2 := by
    apply Fintype.sum_equiv (partitionAssignmentEquiv hdisjoint hcover)
    intro input
    exact hsummand input
  have hcard : leftSupport.card + rightSupport.card = n := by
    calc
      leftSupport.card + rightSupport.card =
          (leftSupport ∪ rightSupport).card :=
        (Finset.card_union_of_disjoint hdisjoint).symm
      _ = Finset.univ.card := congrArg Finset.card hcover
      _ = n := by simp
  have hdenominator :
      (2 : ℚ) ^ n =
        (2 : ℚ) ^ leftSupport.card * (2 : ℚ) ^ rightSupport.card := by
    calc
      (2 : ℚ) ^ n = (2 : ℚ) ^ (leftSupport.card + rightSupport.card) :=
        congrArg (fun exponent : Nat => (2 : ℚ) ^ exponent) hcard.symm
      _ = (2 : ℚ) ^ leftSupport.card * (2 : ℚ) ^ rightSupport.card :=
        pow_add 2 leftSupport.card rightSupport.card
  calc
    coefficient
          (fun input =>
            f (restrictAssignment leftSupport input) *
              g (restrictAssignment rightSupport input))
          (liftLocalSupport leftSupport alpha ∪
            liftLocalSupport rightSupport beta) =
        separatedProductCoefficient leftSupport rightSupport f g alpha beta := by
      simp only [coefficient, separatedProductCoefficient]
      change
        (∑ input : Fin n → Bool,
            (f (restrictAssignment leftSupport input) *
                g (restrictAssignment rightSupport input)) *
              character
                (liftLocalSupport leftSupport alpha ∪
                  liftLocalSupport rightSupport beta) input) /
              (2 : ℚ) ^ n =
          (∑ inputs : LocalAssignment leftSupport ×
                LocalAssignment rightSupport,
              leftSummand inputs.1 * rightSummand inputs.2) /
            ((2 : ℚ) ^ leftSupport.card *
              (2 : ℚ) ^ rightSupport.card)
      rw [hsum, hdenominator]
    _ = localCoefficient leftSupport f alpha *
          localCoefficient rightSupport g beta :=
      separatedProductCoefficient_eq_mul_localCoefficient
        leftSupport rightSupport f g alpha beta

/-- Dependency-set form of partition factorization.  It applies directly to
two ambient rational functions whose advertised dependency sets are disjoint
and cover the ambient coordinates. -/
theorem coefficient_mul_eq_mul_localCoefficient_of_partition
    {n : Nat} {leftSupport rightSupport : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) :
    coefficient (fun input => f input * g input)
        (liftLocalSupport leftSupport alpha ∪
          liftLocalSupport rightSupport beta) =
      localCoefficient leftSupport
          (fun input => f (extendAssignment leftSupport input)) alpha *
        localCoefficient rightSupport
          (fun input => g (extendAssignment rightSupport input)) beta := by
  have hfunction :
      (fun input : Fin n → Bool => f input * g input) =
        (fun input =>
          f (extendAssignment leftSupport
              (restrictAssignment leftSupport input)) *
            g (extendAssignment rightSupport
              (restrictAssignment rightSupport input))) := by
    funext input
    rw [← eq_extend_restrict_of_dependsOnlyOn hf input,
      ← eq_extend_restrict_of_dependsOnlyOn hg input]
  rw [hfunction]
  exact coefficient_separatedProduct_eq_mul_localCoefficient_of_partition
    hdisjoint hcover
      (fun input => f (extendAssignment leftSupport input))
      (fun input => g (extendAssignment rightSupport input)) alpha beta

/-- On the left half of a partition, the ambient uniform coefficient is the
corresponding local coefficient.  The other half contributes a normalized
factor of one. -/
theorem coefficient_eq_localCoefficient_left_of_partition
    {n : Nat} {leftSupport rightSupport : Finset (Fin n)}
    {f : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (alpha : Finset ↥leftSupport) :
    coefficient f (liftLocalSupport leftSupport alpha) =
      localCoefficient leftSupport
        (fun input => f (extendAssignment leftSupport input)) alpha := by
  have hone : DependsOnlyOn rightSupport
      (fun _input : Fin n → Bool => (1 : ℚ)) := by
    intro input input' hagrees
    rfl
  have hfactor := coefficient_mul_eq_mul_localCoefficient_of_partition
    hf hone hdisjoint hcover alpha (∅ : Finset ↥rightSupport)
  simpa [liftLocalSupport, localCoefficient, localCharacter] using hfactor

/-- Right-handed version of `coefficient_eq_localCoefficient_left_of_partition`. -/
theorem coefficient_eq_localCoefficient_right_of_partition
    {n : Nat} {leftSupport rightSupport : Finset (Fin n)}
    {g : (Fin n → Bool) → ℚ}
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (beta : Finset ↥rightSupport) :
    coefficient g (liftLocalSupport rightSupport beta) =
      localCoefficient rightSupport
        (fun input => g (extendAssignment rightSupport input)) beta := by
  have hone : DependsOnlyOn leftSupport
      (fun _input : Fin n → Bool => (1 : ℚ)) := by
    intro input input' hagrees
    rfl
  have hfactor := coefficient_mul_eq_mul_localCoefficient_of_partition
    hone hg hdisjoint hcover (∅ : Finset ↥leftSupport) beta
  simpa [liftLocalSupport, localCoefficient, localCharacter] using hfactor

/-- Ambient coefficient factorization when the two dependency sets form a
partition of all coordinates. -/
theorem coefficient_mul_eq_mul_coefficient_of_partition
    {n : Nat} {leftSupport rightSupport : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (hcover : leftSupport ∪ rightSupport = Finset.univ)
    (alpha : Finset ↥leftSupport) (beta : Finset ↥rightSupport) :
    coefficient (fun input => f input * g input)
        (liftLocalSupport leftSupport alpha ∪
          liftLocalSupport rightSupport beta) =
      coefficient f (liftLocalSupport leftSupport alpha) *
        coefficient g (liftLocalSupport rightSupport beta) := by
  calc
    coefficient (fun input => f input * g input)
          (liftLocalSupport leftSupport alpha ∪
            liftLocalSupport rightSupport beta) =
        localCoefficient leftSupport
            (fun input => f (extendAssignment leftSupport input)) alpha *
          localCoefficient rightSupport
            (fun input => g (extendAssignment rightSupport input)) beta :=
      coefficient_mul_eq_mul_localCoefficient_of_partition
        hf hg hdisjoint hcover alpha beta
    _ = coefficient f (liftLocalSupport leftSupport alpha) *
          coefficient g (liftLocalSupport rightSupport beta) := by
      rw [coefficient_eq_localCoefficient_left_of_partition
          hf hdisjoint hcover alpha,
        coefficient_eq_localCoefficient_right_of_partition
          hg hdisjoint hcover beta]

/-- Exact factorization for arbitrary disjoint dependency sets.  No covering
assumption is needed: coordinates outside both sets are assigned to the right
side of the complementary partition and cancel under uniform normalization. -/
theorem coefficient_mul_eq_mul_coefficient_of_disjoint
    {n : Nat} {leftSupport rightSupport alpha : Finset (Fin n)}
    {f g : (Fin n → Bool) → ℚ}
    (hf : DependsOnlyOn leftSupport f)
    (hg : DependsOnlyOn rightSupport g)
    (hdisjoint : Disjoint leftSupport rightSupport)
    (halpha : alpha ⊆ leftSupport ∪ rightSupport) :
    coefficient (fun input => f input * g input) alpha =
      coefficient f (alpha ∩ leftSupport) *
        coefficient g (alpha ∩ rightSupport) := by
  have hpartitionDisjoint :
      Disjoint leftSupport (Finset.univ \ leftSupport) := by
    rw [Finset.disjoint_left]
    intro queryIndex hleft
    simp [hleft]
  have hpartitionCover :
      leftSupport ∪ (Finset.univ \ leftSupport) = Finset.univ := by
    ext queryIndex
    simp
  have hrightSubset :
      rightSupport ⊆ Finset.univ \ leftSupport := by
    intro queryIndex hright
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
    intro hleft
    exact (Finset.disjoint_left.mp hdisjoint hleft) hright
  have hgComplement :
      DependsOnlyOn (Finset.univ \ leftSupport) g :=
    dependsOnlyOn_mono hrightSubset hg
  have hpartition := coefficient_mul_eq_mul_coefficient_of_partition
    hf hgComplement hpartitionDisjoint hpartitionCover
      (localizeSupport leftSupport alpha)
      (localizeSupport (Finset.univ \ leftSupport) alpha)
  have hunion :
      (alpha ∩ leftSupport) ∪
          (alpha ∩ (Finset.univ \ leftSupport)) = alpha := by
    ext queryIndex
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff,
      Finset.mem_univ, true_and]
    tauto
  have hright :
      alpha ∩ (Finset.univ \ leftSupport) =
        alpha ∩ rightSupport := by
    ext queryIndex
    simp only [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hqueryAlpha, hqueryNotLeft⟩
      have hqueryUnion := halpha hqueryAlpha
      rcases Finset.mem_union.mp hqueryUnion with hqueryLeft | hqueryRight
      · exact (hqueryNotLeft hqueryLeft).elim
      · exact ⟨hqueryAlpha, hqueryRight⟩
    · rintro ⟨hqueryAlpha, hqueryRight⟩
      refine ⟨hqueryAlpha, ?_⟩
      intro hqueryLeft
      exact (Finset.disjoint_left.mp hdisjoint hqueryLeft) hqueryRight
  have hunionOriginal :
      (alpha ∩ leftSupport) ∪ (alpha ∩ rightSupport) = alpha := by
    rw [← hright]
    exact hunion
  simpa only [liftLocalSupport_localizeSupport, hright, hunionOriginal] using
    hpartition

end FiniteBooleanFourier
end OneTapeMagnification
end Frontier
end Pnp4
