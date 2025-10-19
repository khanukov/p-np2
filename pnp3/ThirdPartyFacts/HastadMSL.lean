import Core.BooleanBasics
import Core.PDTPartial
import Core.ShrinkageWitness
import ThirdPartyFacts.BaseSwitching
import ThirdPartyFacts.SwitchingParameters

/-!
  This module isolates the exact interface of the multi-switching lemma in a
  reusable Lean structure.  The actual existence proof lives in
  `ThirdPartyFacts.Facts_Switching`, so this file only introduces the data
  container and helper constructors.  Keeping the statement separate from the
  proof strategy makes it straightforward to replace axioms by constructive
  arguments as soon as they become available.
-/

namespace Pnp3
namespace ThirdPartyFacts

open Core

/-- Список всех точечных подкубов на `n` переменных. -/
noncomputable def pointLeafList (n : Nat) : List (Subcube n) :=
  (Core.bitVecList n).map Core.pointSubcube

lemma mem_pointLeafList {n : Nat} (x : Core.BitVec n) :
    Core.pointSubcube x ∈ pointLeafList n := by
  classical
  unfold pointLeafList
  have hx : x ∈ Core.bitVecList n := Core.mem_bitVecList x
  exact List.mem_map.mpr ⟨x, hx, rfl⟩

lemma pointLeafList_ne_nil (n : Nat) : pointLeafList n ≠ [] := by
  classical
  intro hnil
  have hx : Core.pointSubcube (fun _ : Fin n => false) ∈ pointLeafList n :=
    mem_pointLeafList (n := n) (x := fun _ => false)
  have hnonempty := List.ne_nil_of_mem hx
  exact hnonempty hnil

lemma bitVecList_length (n : Nat) :
    (Core.bitVecList n).length = Nat.pow 2 n := by
  classical
  have hcard : Fintype.card (Core.BitVec n) = Nat.pow 2 n := by
    simpa [Core.BitVec, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool]
      using
      (Fintype.card_fun (α := Fin n) (β := Bool))
  have hfinset :
      (Finset.univ : Finset (Core.BitVec n)).card = Nat.pow 2 n := by
    simpa [hcard] using
      (Finset.card_univ :
        (Finset.univ : Finset (Core.BitVec n)).card = Fintype.card _)
  have := Finset.length_toList (s := (Finset.univ : Finset (Core.BitVec n)))
  simpa [Core.bitVecList, hfinset] using this

lemma pointLeafList_length (n : Nat) :
    (pointLeafList n).length = Nat.pow 2 n := by
  classical
  unfold pointLeafList
  simpa [List.length_map, bitVecList_length]

/-- Канонический ствол PDT, содержащий все точечные подкубы. -/
noncomputable def canonicalTrunk (n : Nat) : Core.PDT n :=
  Core.PDT.ofLeafList (pointLeafList n)

lemma canonicalTrunk_leaves_succ {n : Nat} :
    Core.PDT.leaves (canonicalTrunk (Nat.succ n))
      = pointLeafList (Nat.succ n) := by
  classical
  unfold canonicalTrunk pointLeafList
  have hlist :
      (Core.bitVecList (Nat.succ n)).map Core.pointSubcube ≠ [] := by
    intro hnil
    have hx : Core.pointSubcube (fun _ : Fin (Nat.succ n) => false)
        ∈ (Core.bitVecList (Nat.succ n)).map Core.pointSubcube :=
      by
        refine List.mem_map.mpr ?_
        exact ⟨fun _ : Fin (Nat.succ n) => false,
          by simpa using Core.mem_bitVecList (x := fun _ => false), rfl⟩
    have hnonempty := List.ne_nil_of_mem hx
    exact hnonempty hnil
  exact Core.PDT.leaves_ofLeafList_nonempty
    (n := n)
    (L := (Core.bitVecList (Nat.succ n)).map Core.pointSubcube)
    hlist

lemma canonicalTrunk_leaves_zero :
    Core.PDT.leaves (canonicalTrunk 0)
      = pointLeafList 0 := by
  classical
  unfold canonicalTrunk pointLeafList
  -- Для нулевого числа переменных вектора битов образуют однозначный список,
  -- так что после отображения через `pointSubcube` остаётся ровно один лист.
  have hlen_bitVec : (Core.bitVecList 0).length = 1 := by
    have hcardBitVec :
        (Finset.univ : Finset (Core.BitVec 0)).card = 1 := by
      have hcard : Fintype.card (Core.BitVec 0) = 1 := by
        -- `BitVec 0` — это `Fin 0 → Bool`, а значит, мощность равна `2^0 = 1`.
        simpa [Core.BitVec, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool,
          Nat.pow_zero]
      simpa [hcard] using
        (Finset.card_univ :
          (Finset.univ : Finset (Core.BitVec 0)).card =
            Fintype.card (Core.BitVec 0))
    -- Переводим оценку мощности к длине списка `bitVecList`.
    have := Finset.length_toList
      (s := (Finset.univ : Finset (Core.BitVec 0)))
    simpa [Core.bitVecList, hcardBitVec] using this
  have hlen_map :
      ((Core.bitVecList 0).map Core.pointSubcube).length = 1 := by
    simpa [List.length_map] using hlen_bitVec
  -- Списки длины 1 равны некоторому одноэлементному списку `[β]`.
  rcases List.length_eq_one_iff.mp hlen_map with ⟨β, hβ⟩
  -- После раскрытия `PDT.ofLeafList` и подстановки `[β]` оба края равенства
  -- сводятся к `[β]`.
  simpa [hβ] using
    (Core.PDT.leaves_ofLeafList_singleton (β := β))

lemma pointSubcube_mem_canonical {n : Nat} (x : Core.BitVec n) :
    Core.pointSubcube x ∈ Core.PDT.leaves (canonicalTrunk n) := by
  classical
  cases n with
  | zero =>
      simpa [canonicalTrunk_leaves_zero]
        using (mem_pointLeafList (n := 0) (x := x))
  | succ n =>
      have := mem_pointLeafList (n := Nat.succ n) (x := x)
      have hleaves := canonicalTrunk_leaves_succ (n := n)
      simpa [hleaves] using this

lemma canonicalTrunk_depth_le_pow (n : Nat) :
    Core.PDT.depth (canonicalTrunk n) ≤ Nat.pow 2 n := by
  classical
  unfold canonicalTrunk
  have := Core.PDT.depth_ofLeafList_le_length (L := pointLeafList n)
  simpa [pointLeafList_length] using this

/-- Тривиальный частичный сертификат: ствол содержит все точки, ошибка равна нулю. -/
noncomputable def pointPartialCertificate
    (n : Nat) (F : Family n) :
    Core.PartialCertificate n 0 F :=
    { witness := Core.PartialDT.ofPDT (canonicalTrunk n)
      depthBound := Core.PDT.depth (canonicalTrunk n)
      epsilon := 0
      trunk_depth_le := by
        exact le_rfl
      selectors := fun f => Core.pointSelectors f
      selectors_sub := by
        intro f β hf hβ
        classical
        unfold Core.pointSelectors at hβ
        obtain ⟨x, _, hxEq⟩ := List.mem_map.mp hβ
        subst hxEq
        have hxLeaf := pointSubcube_mem_canonical (n := n) (x := x)
        change Core.pointSubcube x ∈
            Core.PDT.leaves (Core.PartialDT.ofPDT (canonicalTrunk n)).realize
        have hrealize :
            Core.PDT.leaves (Core.PartialDT.ofPDT (canonicalTrunk n)).realize =
              Core.PDT.leaves (canonicalTrunk n) := by
          simpa [Core.PartialDT.realize_ofPDT]
        exact Eq.subst
          (motive := fun L => Core.pointSubcube x ∈ L)
          hrealize.symm hxLeaf
      err_le := by
        intro f hf
        have herr := Core.errU_pointSelectors_eq_zero (n := n) (f := f)
        simpa [herr] using (show (0 : Core.Q) ≤ 0 by exact le_rfl) }

lemma pointPartialCertificate_depth_le
    (n : Nat) (F : Family n) :
    (pointPartialCertificate n F).depthBound ≤ Nat.pow 2 n := by
  classical
  simpa [pointPartialCertificate]
    using canonicalTrunk_depth_le_pow (n := n)

/--
  Result of the multi-switching lemma specialised to AC⁰ formulas.  The record
  intentionally mirrors the shape of `Core.PartialCertificate` but keeps all
  numeric bounds in explicitly named fields that match the informal literature.

  * `level`    – maximal depth of the individual tails attached to each leaf of
                 the common PDT trunk.
  * `trunk`    – partial decision tree on the full set of variables.
  * `tails`    – witnesses providing a tail of depth at most `level` for each
                 leaf of the trunk.
  * `selectors` – family-specific selector lists that control the uniform error.

  The fields `level_le_log`, `depth_trunk_le` and `epsilon_bound` encode the
  quantitative guarantees promised by the multi-switching lemma.
-/
@[ext] structure MultiSwitchingWitness
    (params : AC0Parameters) (F : Family params.n) where
  /-- Maximum tail depth supplied by the multi-switching lemma. -/
  level           : Nat
  /-- Partial decision tree assembled from the common trunk and the tails. -/
  certificate     : Core.PartialCertificate params.n level F
  /-- Depth of each tail is at most `level`, matching the literature. -/
  tail_depth_le   : ∀ β hβ, PDT.depth (certificate.witness.tails β hβ) ≤ level
  /-- Quantitative upper bound on the allowed tail depth. -/
  level_le_log    : level ≤ Nat.log2 (params.M + 2)
  /-- Overall trunk depth bound promised by the lemma. -/
  depth_trunk_le  : certificate.depthBound + level
      ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1)
  /-- Non-negativity of the approximation error. -/
  epsilon_nonneg  : (0 : Core.Q) ≤ certificate.epsilon
  /-- Uniform error is bounded by `1/(n+2)`. -/
  epsilon_bound   : certificate.epsilon ≤ (1 : Core.Q) / (params.n + 2)

attribute [simp] MultiSwitchingWitness.level MultiSwitchingWitness.certificate

/--
  Helper constructor: whenever we already know a partial certificate together
  with the numerical bounds promised by the multi-switching lemma, we can
  package this data into a `MultiSwitchingWitness`.  This wrapper is useful
  during the refactor that will ultimately replace the axiomatic lemma by a
  constructive proof: intermediate stages often manage to build the partial
  certificate first and only later discharge the quantitative obligations.

  The function makes the conversion explicit so that upcoming proofs can reuse
  it without duplicating boilerplate.
-/
noncomputable def MultiSwitchingWitness.ofPartialCertificate
    {params : AC0Parameters} {F : Family params.n}
    {ℓ : Nat}
    (C : Core.PartialCertificate params.n ℓ F)
    (hlevel : ℓ ≤ Nat.log2 (params.M + 2))
    (hdepth : C.depthBound + ℓ
        ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1))
    (hε_nonneg : (0 : Core.Q) ≤ C.epsilon)
    (hε_bound : C.epsilon ≤ (1 : Core.Q) / (params.n + 2)) :
    MultiSwitchingWitness params F :=
  { level := ℓ
    certificate := C
    tail_depth_le := C.witness.tail_depth_le
    level_le_log := hlevel
    depth_trunk_le := hdepth
    epsilon_nonneg := hε_nonneg
    epsilon_bound := hε_bound }

--  The general multi-switching witness is now provided by
--  `ThirdPartyFacts.Facts_Switching.hastad_multiSwitching`, which packages the
--  partial shrinkage axiom into the structure introduced above.  We keep the
--  explicit empty-family witness here for quick sanity checks.

/--
  Explicit witness for the empty family.  The trunk is a single leaf covering
  the whole cube, tails are trivial, and selectors are absent because there is
  nothing to approximate.  All quantitative bounds hold automatically.
-/
noncomputable def emptyMultiSwitching
    (params : AC0Parameters) :
    MultiSwitchingWitness params ([] : Family params.n) := by
  classical
  -- Trivial partial certificate with a single leaf.
  let trunk : Core.PDT params.n :=
    Core.PDT.leaf (fun _ => none)
  let witness : Core.PartialDT params.n 0 :=
    Core.PartialDT.ofPDT trunk
  refine
    { level := 0
      certificate :=
        { witness := witness
          depthBound := 0
          epsilon := 0
          trunk_depth_le := by
            -- Depth of the leaf is zero by definition.
            simp [witness, Core.PartialDT.ofPDT, trunk, Core.PDT.depth]
          selectors := fun _ => []
          selectors_sub := by
            intro f β hf
            -- `hf` is impossible because the family is empty.
            cases hf
          err_le := by
            intro f hf
            cases hf }
      tail_depth_le := by
        intro β hβ
        -- Tails are leaves as well, hence depth zero.
        simp [witness, Core.PartialDT.ofPDT, Core.PDT.depth]
      level_le_log := by
        -- `0 ≤ log₂(M+2)` for every `M`.
        simpa using (Nat.zero_le _ : 0 ≤ Nat.log2 (params.M + 2))
      depth_trunk_le := by
        -- Trunk depth is zero, so the bound is immediate.
        have : (0 : Nat)
            ≤ Nat.pow (Nat.log2 (params.M + 2)) (params.d + 1) :=
          Nat.zero_le _
        simpa using this
      epsilon_nonneg := by
        -- Error is exactly zero.
        simpa using (le_of_eq (rfl : (0 : Core.Q) = 0))
      epsilon_bound := by
        -- And `0 ≤ 1/(n+2)` holds universally.
        have hden : (0 : Core.Q) < (params.n + 2 : Core.Q) := by
          have : (0 : Nat) < params.n + 2 :=
            Nat.succ_pos (params.n + 1)
          exact_mod_cast this
        have hnum : (0 : Core.Q) ≤ (1 : Core.Q) := by
          exact zero_le_one
        have hpos : (0 : Core.Q) ≤ (1 : Core.Q) / (params.n + 2 : Core.Q) :=
          div_nonneg hnum (le_of_lt hden)
        simpa using hpos }

end ThirdPartyFacts
end Pnp3
