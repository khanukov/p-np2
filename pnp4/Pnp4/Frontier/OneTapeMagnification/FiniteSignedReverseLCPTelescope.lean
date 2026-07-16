import Pnp4.Frontier.OneTapeMagnification.MandatoryCanonicalSelectorReverseLCPBucket
import Pnp4.Frontier.OneTapeMagnification.FiniteSignedResidualAcceptedModelPairKernel

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Exact signed reverse-LCP telescope

The maximal reverse-LCP buckets and residual rectangles control compatible
model counts, but the residual deviation is a signed sum over **all** accepted
models: an incompatible model still contributes the negative of its
low-degree predictor.  Consequently a nonnegative sum of compatible-bucket
capacities cannot by itself bound the signed second moment.

This file supplies the exact missing algebraic bridge.  For an arbitrary
finite family of traces and rational atomic weights, let `A(key)` be the total
weight in the suffix cone above `key`.  The charge of pairs whose exact
longest common suffix is `key` is

```text
A(key)^2 - sum_symbol A(symbol :: key)^2.
```

Thus the exact-LCP charges telescope across the reverse trace trie with no
factor for the number of path positions.  We specialize the identity to the
canonical full traces of a finite uFBDD and to the signed accepted-point
residual deviations.  This includes every accepted model, compatible or not.

No numerical correlation estimate is asserted here.  The remaining analytic
obligation is a one-sided potential/Carleson inequality for these signed
square drops under the structured short seed.  The existing rectangle
capacity does not imply such an inequality after absolute values.
-/

noncomputable section

open scoped BigOperators

namespace FiniteSignedReverseLCPTelescope

/-! ## Generic finite prefix and suffix tries -/

/-- Total rational weight in a prefix cone. -/
def prefixConeMass
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) : Rat :=
  ∑ index : Index, if key <+: trace index then weight index else 0

/-- Signed charge of ordered pairs having one exact longest common prefix. -/
def exactLCPPairCharge
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) : Rat :=
  ∑ left : Index, ∑ right : Index,
    if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
        (trace left) (trace right) = key then
      weight left * weight right
    else 0

/-- Removing a common literal prefix commutes with longest-common-prefix. -/
theorem longestCommonPrefix_append_left
    {Alphabet : Type*} [DecidableEq Alphabet]
    (key left right : List Alphabet) :
    FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
        (key ++ left) (key ++ right) =
      key ++ FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix left right := by
  induction key with
  | nil => rfl
  | cons head tail ih =>
      simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix, ih]

/-- Prefix cancellation for one immediate extension of a common prefix. -/
theorem append_singleton_isPrefix_append_iff
    {Alphabet : Type*} (key rest : List Alphabet) (symbol : Alphabet) :
    key ++ [symbol] <+: key ++ rest <-> [symbol] <+: rest := by
  constructor
  · rintro ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    simpa [List.append_assoc] using htail
  · rintro ⟨tail, htail⟩
    refine ⟨tail, ?_⟩
    simp [List.append_assoc, htail]

/-- Pointwise partition of a common-prefix pair into its exact-LCP cell or
one unique immediate common child cone. -/
theorem exactLCPIndicator_eq_commonPrefix_sub_children
    {Alphabet : Type*} [DecidableEq Alphabet]
    (left right key : List Alphabet) (symbols : Finset Alphabet)
    (hcovers : ∀ symbol : Alphabet,
      key ++ [symbol] <+: left -> symbol ∈ symbols) :
    (if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix left right = key
        then (1 : Rat) else 0) =
      (if key <+: left ∧ key <+: right then (1 : Rat) else 0) -
        ∑ symbol ∈ symbols,
          if key ++ [symbol] <+: left ∧ key ++ [symbol] <+: right
          then (1 : Rat) else 0 := by
  classical
  by_cases hleft : key <+: left
  · rcases hleft with ⟨leftRest, hleft⟩
    rw [← hleft]
    by_cases hright : key <+: right
    · rcases hright with ⟨rightRest, hright⟩
      rw [← hright]
      rw [longestCommonPrefix_append_left]
      cases leftRest with
      | nil =>
          have hnotExtended : ∀ symbol : Alphabet,
              ¬ (key ++ [symbol] <+: key) := by
            intro symbol hprefix
            have hlength := hprefix.length_le
            simp at hlength
          simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix,
            hnotExtended]
      | cons leftHead leftTail =>
          cases rightRest with
          | nil =>
              have hnotExtended : ∀ symbol : Alphabet,
                  ¬ (key ++ [symbol] <+: key) := by
                intro symbol hprefix
                have hlength := hprefix.length_le
                simp at hlength
              simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix,
                hnotExtended]
          | cons rightHead rightTail =>
              by_cases hhead : leftHead = rightHead
              · subst rightHead
                have hleftExtended :
                    key ++ [leftHead] <+: key ++ leftHead :: leftTail := by
                  refine ⟨leftTail, ?_⟩
                  simp [List.append_assoc]
                have hleftMem : leftHead ∈ symbols :=
                  hcovers leftHead (by
                    rw [← hleft]
                    exact hleftExtended)
                simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix,
                  hleftMem]
              · have hnoCommonHead : ∀ symbol : Alphabet,
                    ¬ (symbol = leftHead ∧ symbol = rightHead) := by
                  intro symbol hboth
                  exact hhead (hboth.1.symm.trans hboth.2)
                simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix,
                  hhead,
                  hnoCommonHead]
    · have hlcpNe :
          FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
              (key ++ leftRest) right ≠ key := by
          intro heq
          apply hright
          rw [← heq]
          exact
            FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix_isPrefix_right
              (key ++ leftRest) right
      have hchild : ∀ symbol : Alphabet,
          ¬ (key ++ [symbol] <+: right) := by
        intro symbol hextended
        apply hright
        exact (show key <+: key ++ [symbol] from ⟨[symbol], rfl⟩).trans hextended
      simp [hlcpNe, hright, hchild]
  · have hlcpNe :
        FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix left right ≠ key := by
        intro heq
        apply hleft
        rw [← heq]
        exact
          FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix_isPrefix_left
            left right
    have hchild : ∀ symbol : Alphabet,
        ¬ (key ++ [symbol] <+: left) := by
      intro symbol hextended
      apply hleft
      exact (show key <+: key ++ [symbol] from ⟨[symbol], rfl⟩).trans hextended
    simp [hlcpNe, hleft, hchild]

/-- Alphabet symbols which actually occur as an immediate extension of
`key` in one of the finite traces.  No ambient `Fintype Alphabet` instance is
needed. -/
def nextPrefixSymbols
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (key : List Alphabet) :
    Finset Alphabet :=
  (Finset.univ : Finset Index).biUnion fun index =>
    (trace index).toFinset.filter fun symbol =>
      key ++ [symbol] <+: trace index

theorem mem_nextPrefixSymbols_of_isPrefix
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (key : List Alphabet)
    (index : Index) (symbol : Alphabet)
    (hprefix : key ++ [symbol] <+: trace index) :
    symbol ∈ nextPrefixSymbols trace key := by
  classical
  have hmem : symbol ∈ trace index := by
    rcases hprefix with ⟨tail, htail⟩
    rw [← htail]
    simp
  unfold nextPrefixSymbols
  apply Finset.mem_biUnion.mpr
  refine ⟨index, Finset.mem_univ _, ?_⟩
  simp [hmem, hprefix]

/-- Expanding a cone square gives the ordered-pair sum over the same cone. -/
theorem prefixConeMass_sq_eq_pairSum
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    prefixConeMass trace weight key ^ 2 =
      ∑ left : Index, ∑ right : Index,
        if key <+: trace left ∧ key <+: trace right then
          weight left * weight right
        else 0 := by
  classical
  unfold prefixConeMass
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  by_cases hleft : key <+: trace left <;>
    by_cases hright : key <+: trace right <;>
      simp [hleft, hright]

/-- Weighted form of the pointwise exact-LCP partition. -/
theorem exactLCPWeightedIndicator_eq_commonPrefix_sub_children
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) (left right : Index) :
    (if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
          (trace left) (trace right) = key then
        weight left * weight right
      else 0) =
      (if key <+: trace left ∧ key <+: trace right then
        weight left * weight right
      else 0) -
        ∑ symbol ∈ nextPrefixSymbols trace key,
          if key ++ [symbol] <+: trace left ∧
              key ++ [symbol] <+: trace right then
            weight left * weight right
          else 0 := by
  classical
  have hindicator := exactLCPIndicator_eq_commonPrefix_sub_children
    (trace left) (trace right) key (nextPrefixSymbols trace key)
    (fun symbol hprefix =>
      mem_nextPrefixSymbols_of_isPrefix trace key left symbol hprefix)
  calc
    (if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
          (trace left) (trace right) = key then
        weight left * weight right
      else 0) =
      (if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
          (trace left) (trace right) = key then (1 : Rat) else 0) *
        (weight left * weight right) := by
          split <;> simp
    _ = ((if key <+: trace left ∧ key <+: trace right
          then (1 : Rat) else 0) -
        ∑ symbol ∈ nextPrefixSymbols trace key,
          if key ++ [symbol] <+: trace left ∧
              key ++ [symbol] <+: trace right
          then (1 : Rat) else 0) *
        (weight left * weight right) := by rw [hindicator]
    _ = _ := by
      rw [sub_mul, Finset.sum_mul]
      apply congrArg₂ (fun leftValue rightValue => leftValue - rightValue)
      · split <;> simp
      · apply Finset.sum_congr rfl
        intro symbol hsymbol
        split <;> simp

/-- Local exact signed telescope on a finite prefix trie. -/
theorem exactLCPPairCharge_eq_prefixConeMass_sq_sub_children
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    exactLCPPairCharge trace weight key =
      prefixConeMass trace weight key ^ 2 -
        ∑ symbol ∈ nextPrefixSymbols trace key,
          prefixConeMass trace weight (key ++ [symbol]) ^ 2 := by
  classical
  rw [prefixConeMass_sq_eq_pairSum]
  unfold exactLCPPairCharge
  calc
    (∑ left : Index, ∑ right : Index,
        if FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
            (trace left) (trace right) = key then
          weight left * weight right
        else 0) =
      ∑ left : Index, ∑ right : Index,
        ((if key <+: trace left ∧ key <+: trace right then
            weight left * weight right
          else 0) -
          ∑ symbol ∈ nextPrefixSymbols trace key,
            if key ++ [symbol] <+: trace left ∧
                key ++ [symbol] <+: trace right then
              weight left * weight right
            else 0) := by
              apply Finset.sum_congr rfl
              intro left _
              apply Finset.sum_congr rfl
              intro right _
              exact exactLCPWeightedIndicator_eq_commonPrefix_sub_children
                trace weight key left right
    _ = (∑ left : Index, ∑ right : Index,
          if key <+: trace left ∧ key <+: trace right then
            weight left * weight right
          else 0) -
        ∑ left : Index, ∑ right : Index,
          ∑ symbol ∈ nextPrefixSymbols trace key,
            if key ++ [symbol] <+: trace left ∧
                key ++ [symbol] <+: trace right then
              weight left * weight right
            else 0 := by
              simp_rw [Finset.sum_sub_distrib]
    _ = (∑ left : Index, ∑ right : Index,
          if key <+: trace left ∧ key <+: trace right then
            weight left * weight right
          else 0) -
        ∑ symbol ∈ nextPrefixSymbols trace key,
          ∑ left : Index, ∑ right : Index,
            if key ++ [symbol] <+: trace left ∧
                key ++ [symbol] <+: trace right then
              weight left * weight right
            else 0 := by
              congr 1
              calc
                (∑ left : Index, ∑ right : Index,
                    ∑ symbol ∈ nextPrefixSymbols trace key,
                      if key ++ [symbol] <+: trace left ∧
                          key ++ [symbol] <+: trace right then
                        weight left * weight right
                      else 0) =
                  ∑ left : Index,
                    ∑ symbol ∈ nextPrefixSymbols trace key,
                      ∑ right : Index,
                        if key ++ [symbol] <+: trace left ∧
                            key ++ [symbol] <+: trace right then
                          weight left * weight right
                        else 0 := by
                          apply Finset.sum_congr rfl
                          intro left _
                          rw [Finset.sum_comm]
                _ = ∑ symbol ∈ nextPrefixSymbols trace key,
                    ∑ left : Index, ∑ right : Index,
                      if key ++ [symbol] <+: trace left ∧
                          key ++ [symbol] <+: trace right then
                        weight left * weight right
                      else 0 := by
                          rw [Finset.sum_comm]
    _ = (∑ left : Index, ∑ right : Index,
          if key <+: trace left ∧ key <+: trace right then
            weight left * weight right
          else 0) -
        ∑ symbol ∈ nextPrefixSymbols trace key,
          prefixConeMass trace weight (key ++ [symbol]) ^ 2 := by
              apply congrArg (fun childValue =>
                (∑ left : Index, ∑ right : Index,
                  if key <+: trace left ∧ key <+: trace right then
                    weight left * weight right
                  else 0) - childValue)
              apply Finset.sum_congr rfl
              intro symbol _
              rw [prefixConeMass_sq_eq_pairSum]

/-- Total rational weight in a forward suffix cone. -/
def suffixConeMass
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) : Rat :=
  ∑ index : Index, if key <:+ trace index then weight index else 0

/-- Signed charge of ordered pairs having one exact longest common suffix. -/
def exactLCSPairCharge
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) : Rat :=
  ∑ left : Index, ∑ right : Index,
    if FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
        (trace left) (trace right) = key then
      weight left * weight right
    else 0

/-- The finite set of symbols which occur immediately before one realized
suffix cone.  Reversing turns this into the corresponding prefix-trie
frontier. -/
def nextSuffixSymbols
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (key : List Alphabet) :
    Finset Alphabet :=
  nextPrefixSymbols (fun index => (trace index).reverse) key.reverse

/-- A suffix cone is the corresponding prefix cone after reversing every
trace and the key. -/
theorem suffixConeMass_eq_prefixConeMass_reverse
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    suffixConeMass trace weight key =
      prefixConeMass (fun index => (trace index).reverse) weight key.reverse := by
  classical
  unfold suffixConeMass prefixConeMass
  apply Finset.sum_congr rfl
  intro index _
  have hiff :
      key <:+ trace index <-> key.reverse <+: (trace index).reverse :=
    (List.reverse_prefix (l₁ := key) (l₂ := trace index)).symm
  by_cases hsuffix : key <:+ trace index
  · have hprefix : key.reverse <+: (trace index).reverse := hiff.mp hsuffix
    simp [hsuffix, hprefix]
  · have hprefix : ¬ key.reverse <+: (trace index).reverse := by
      exact fun h => hsuffix (hiff.mpr h)
    simp [hsuffix, hprefix]

/-- Exact longest-common-suffix charge is exact longest-common-prefix charge
on the reversed traces. -/
theorem exactLCSPairCharge_eq_exactLCPPairCharge_reverse
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    exactLCSPairCharge trace weight key =
      exactLCPPairCharge (fun index => (trace index).reverse)
        weight key.reverse := by
  classical
  unfold exactLCSPairCharge exactLCPPairCharge
  apply Finset.sum_congr rfl
  intro left _
  apply Finset.sum_congr rfl
  intro right _
  simp only [FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix]
  let commonPrefix :=
    FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix
      (trace left).reverse (trace right).reverse
  by_cases hsuffix : commonPrefix.reverse = key
  · have hprefix : commonPrefix = key.reverse := by
      simpa using congrArg List.reverse hsuffix
    simp [commonPrefix, hprefix]
  · have hprefix : commonPrefix ≠ key.reverse := by
      intro heq
      apply hsuffix
      simpa using congrArg List.reverse heq
    simp [commonPrefix, hsuffix, hprefix]

/-- Local exact signed telescope on a finite suffix trie. -/
theorem exactLCSPairCharge_eq_suffixConeMass_sq_sub_children
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    exactLCSPairCharge trace weight key =
      suffixConeMass trace weight key ^ 2 -
        ∑ symbol ∈ nextSuffixSymbols trace key,
          suffixConeMass trace weight (symbol :: key) ^ 2 := by
  classical
  rw [exactLCSPairCharge_eq_exactLCPPairCharge_reverse]
  rw [exactLCPPairCharge_eq_prefixConeMass_sq_sub_children]
  rw [suffixConeMass_eq_prefixConeMass_reverse]
  unfold nextSuffixSymbols
  apply congrArg (fun childValue =>
    prefixConeMass (fun index => (trace index).reverse) weight key.reverse ^ 2 -
      childValue)
  apply Finset.sum_congr rfl
  intro symbol _
  rw [suffixConeMass_eq_prefixConeMass_reverse]
  simp only [List.reverse_cons]

/-- All exact longest-common-suffix keys realized by ordered pairs in the
finite trace family.  Unlike the compatible reverse-LCP buckets, this set
contains the key of every ordered pair. -/
def realizedLCSKeys
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) : Finset (List Alphabet) :=
  (Finset.univ.product Finset.univ).image fun pair =>
    FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
      (trace pair.1) (trace pair.2)

theorem longestCommonSuffix_mem_realizedLCSKeys
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (left right : Index) :
    FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
        (trace left) (trace right) ∈ realizedLCSKeys trace := by
  classical
  unfold realizedLCSKeys
  apply Finset.mem_image.mpr
  exact ⟨(left, right), by simp, rfl⟩

/-- The realized exact-LCS cells partition all ordered pairs.  Consequently
their signed charges sum to the square of the total atomic weight. -/
theorem sum_exactLCSPairCharge_realizedLCSKeys_eq_totalWeight_sq
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat) :
    (∑ key ∈ realizedLCSKeys trace,
        exactLCSPairCharge trace weight key) =
      (∑ index : Index, weight index) ^ 2 := by
  classical
  unfold exactLCSPairCharge
  calc
    (∑ key ∈ realizedLCSKeys trace,
        ∑ left : Index, ∑ right : Index,
          if FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
              (trace left) (trace right) = key then
            weight left * weight right
          else 0) =
      ∑ left : Index, ∑ right : Index,
        ∑ key ∈ realizedLCSKeys trace,
          if FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
              (trace left) (trace right) = key then
            weight left * weight right
          else 0 := by
            calc
              _ = ∑ left : Index, ∑ key ∈ realizedLCSKeys trace,
                    ∑ right : Index,
                      if FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
                          (trace left) (trace right) = key then
                        weight left * weight right
                      else 0 := by
                        rw [Finset.sum_comm]
              _ = _ := by
                apply Finset.sum_congr rfl
                intro left _
                rw [Finset.sum_comm]
    _ = ∑ left : Index, ∑ right : Index,
        weight left * weight right := by
          apply Finset.sum_congr rfl
          intro left _
          apply Finset.sum_congr rfl
          intro right _
          let key :=
            FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
              (trace left) (trace right)
          have hkey : key ∈ realizedLCSKeys trace := by
            exact longestCommonSuffix_mem_realizedLCSKeys trace left right
          rw [Finset.sum_eq_single key]
          · simp [key]
          · intro otherKey hotherKey hne
            have hnot :
                FiniteUnambiguousFBDD.ReverseLCP.longestCommonSuffix
                    (trace left) (trace right) ≠ otherKey := by
              intro heq
              apply hne
              exact heq.symm
            simp [hnot]
          · exact fun hnot => (hnot hkey).elim
    _ = (∑ index : Index, weight index) ^ 2 := by
      rw [pow_two, Finset.sum_mul_sum]

/-- Global exact reverse-trie telescope: summing all realized local square
drops gives the square of the total signed weight. -/
theorem sum_suffixSquareDrops_realizedLCSKeys_eq_totalWeight_sq
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat) :
    (∑ key ∈ realizedLCSKeys trace,
      (suffixConeMass trace weight key ^ 2 -
        ∑ symbol ∈ nextSuffixSymbols trace key,
          suffixConeMass trace weight (symbol :: key) ^ 2)) =
      (∑ index : Index, weight index) ^ 2 := by
  rw [← sum_exactLCSPairCharge_realizedLCSKeys_eq_totalWeight_sq
    trace weight]
  apply Finset.sum_congr rfl
  intro key _
  exact (exactLCSPairCharge_eq_suffixConeMass_sq_sub_children
    trace weight key).symm

end FiniteSignedReverseLCPTelescope

open FiniteBooleanRestrictionMoment

namespace FiniteUnambiguousFBDD

open FiniteSignedReverseLCPTelescope

/-! ## Canonical full-trace specialization -/

/-- Signed residual-deviation mass in one suffix cone of canonical accepting
traces.  The sum ranges over all accepted models, including models which are
incompatible with the frozen cylinder. -/
noncomputable def canonicalResidualDeviationSuffixConeMass {n : Nat}
    (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) : Rat :=
  suffixConeMass B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key

/-- Signed charge of accepted-model pairs having one exact maximal reverse-LCP
key in their canonical full traces. -/
noncomputable def canonicalExactLCPSignedPairCharge {n : Nat}
    (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) : Rat :=
  exactLCSPairCharge B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key

/-- Every maximal reverse-LCP key realized by an ordered pair of accepted
models, with no compatibility filter. -/
noncomputable def canonicalAcceptedPairReverseLCPKeys {n : Nat}
    (B : FiniteUnambiguousFBDD n) :
    Finset (List (InputLabelledFullStep B)) :=
  realizedLCSKeys B.canonicalInputLabelledFullTrace

/-- Realized immediate predecessor steps above a canonical suffix cone. -/
noncomputable def canonicalImmediateReverseLCPSteps {n : Nat}
    (B : FiniteUnambiguousFBDD n) (key : List (InputLabelledFullStep B)) :
    Finset (InputLabelledFullStep B) :=
  nextSuffixSymbols B.canonicalInputLabelledFullTrace key

/-- Expansion of one exact reverse-LCP charge into the existing signed
accepted-model pair kernel. -/
theorem canonicalExactLCPSignedPairCharge_eq_sum_signedPairKernels_on_key
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) :
    B.canonicalExactLCPSignedPairCharge cutoff base mask key =
      ∑ left : B.AcceptedModel, ∑ right : B.AcceptedModel,
        if B.canonicalPairReverseLCPKey (left, right) = key then
          B.signedResidualAcceptedModelPairKernel
            left right cutoff base mask
        else 0 := by
  rfl

/-- The local reverse-trie square drop for canonical accepted-model residual
deviations. -/
theorem canonicalExactLCPSignedPairCharge_eq_suffixSquareDrop
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) :
    B.canonicalExactLCPSignedPairCharge cutoff base mask key =
      B.canonicalResidualDeviationSuffixConeMass
          cutoff base mask key ^ 2 -
        ∑ step ∈ B.canonicalImmediateReverseLCPSteps key,
          B.canonicalResidualDeviationSuffixConeMass
            cutoff base mask (step :: key) ^ 2 := by
  exact exactLCSPairCharge_eq_suffixConeMass_sq_sub_children
    B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key

/-- Summing all realized canonical exact-LCS charges gives the square of the
total signed accepted-point deviation. -/
theorem sum_canonicalExactLCPSignedPairCharges_eq_sum_pointDeviations_sq
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    (∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        B.canonicalExactLCPSignedPairCharge cutoff base mask key) =
      (∑ accepted : B.AcceptedModel,
        B.acceptedPointResidualDeviation accepted cutoff base mask) ^ 2 := by
  exact sum_exactLCSPairCharge_realizedLCSKeys_eq_totalWeight_sq
    B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask)

/-- Capstone pointwise identity: the full residual-deviation square is exactly
the sum of all canonical exact reverse-LCP charges. -/
theorem normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_canonicalExactLCPCharges
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) :
    (B.normalizedResidualAcceptedModelCount base mask -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator cutoff base mask) ^ 2 =
      ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        B.canonicalExactLCPSignedPairCharge cutoff base mask key := by
  rw [B.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_eq_sum_pointDeviations
    cutoff base mask]
  exact
    (B.sum_canonicalExactLCPSignedPairCharges_eq_sum_pointDeviations_sq
      cutoff base mask).symm

/-- Averaging over arbitrary finite base and mask seeds commutes with the
exact reverse-LCP partition.  The key set is structural and seed-independent. -/
theorem residualDeviation_secondMoment_eq_sum_canonicalExactLCPChargeAverages
    {n : Nat} {DSeed TSeed : Type*}
    [Fintype DSeed] [Fintype TSeed] [Nonempty DSeed] [Nonempty TSeed]
    (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (D : DSeed -> Fin n -> Bool) (T : TSeed -> Fin n -> Bool) :
    finiteAverage (fun seed : DSeed × TSeed =>
      (B.normalizedResidualAcceptedModelCount (D seed.1) (T seed.2) -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator cutoff (D seed.1) (T seed.2)) ^ 2) =
      ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        finiteAverage (fun seed : DSeed × TSeed =>
          B.canonicalExactLCPSignedPairCharge cutoff
            (D seed.1) (T seed.2) key) := by
  calc
    finiteAverage (fun seed : DSeed × TSeed =>
        (B.normalizedResidualAcceptedModelCount (D seed.1) (T seed.2) -
          FiniteBooleanResidualMass.maskedLowDegreePredictor
            B.ratAcceptanceIndicator cutoff (D seed.1) (T seed.2)) ^ 2) =
      finiteAverage (fun seed : DSeed × TSeed =>
        ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
          B.canonicalExactLCPSignedPairCharge cutoff
            (D seed.1) (T seed.2) key) := by
              apply finiteAverage_congr
              intro seed
              exact
                B.normalizedResidualAcceptedModelCount_sub_lowDegreePredictor_sq_eq_sum_canonicalExactLCPCharges
                  cutoff (D seed.1) (T seed.2)
    _ = ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        finiteAverage (fun seed : DSeed × TSeed =>
          B.canonicalExactLCPSignedPairCharge cutoff
            (D seed.1) (T seed.2) key) := by
              rw [finiteAverage_finset_sum]

end FiniteUnambiguousFBDD

namespace MandatoryCanonicalSelectorResidualCount

open FiniteUnambiguousFBDD
open DPTWStructuredFullFieldCorrelation
open DPTWStructuredFieldCoordinatePrimitive
open FiniteResidualAcceptedModelCount
open MandatoryCanonicalSelectorPairCorrelation

/-! ## Mandatory prefixed-selector specialization -/

/-- Exact mandatory-selector residual second moment as a sum of averaged
canonical exact reverse-LCP charges. -/
theorem residualModelCountDeviationSecondMoment_eq_sum_canonicalExactLCPChargeAverages
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (normalizedResidualCount machine n T b m tailBits hn htail
          rounds seed -
        residualCountLowDegreePredictor machine n T b m tailBits hn htail
          rounds seed) ^ 2) =
      let B := prefixedMandatoryCanonicalSelector machine n T b rounds
      let D := (structuredUnbiasedPrimitive n m hn).generate
      let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
      ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.canonicalExactLCPSignedPairCharge (2 * m)
            (D seed.1) (mask seed.2) key) := by
  let B := prefixedMandatoryCanonicalSelector machine n T b rounds
  let D := (structuredUnbiasedPrimitive n m hn).generate
  let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
  change
    finiteAverage (fun seed :
        FiniteBitTape (structuredIndependence m * n) ×
          FiniteBitTape (structuredIndependence m * n) =>
      (B.normalizedResidualAcceptedModelCount (D seed.1) (mask seed.2) -
        FiniteBooleanResidualMass.maskedLowDegreePredictor
          B.ratAcceptanceIndicator (2 * m)
            (D seed.1) (mask seed.2)) ^ 2) =
      ∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.canonicalExactLCPSignedPairCharge (2 * m)
            (D seed.1) (mask seed.2) key)
  exact B.residualDeviation_secondMoment_eq_sum_canonicalExactLCPChargeAverages
    (2 * m) D mask

/-- The mandatory selector-pair L2 target is exactly a budget on the averaged
signed charges of the realized maximal reverse-LCP cells.  Proving this
budget is the remaining analytic correlation obligation. -/
theorem residualModelCountL2Bound_iff_canonicalExactLCPChargeBudget
    (machine : DeterministicMachine) [DecidableEq machine.State]
    (n T b m tailBits : Nat) (hn : 0 < n) (htail : tailBits <= n)
    (rounds : List (AffineRestrictionRound (2 ^ n))) :
    ResidualModelCountL2Bound machine n T b m tailBits hn htail rounds <->
      let B := prefixedMandatoryCanonicalSelector machine n T b rounds
      let D := (structuredUnbiasedPrimitive n m hn).generate
      let mask := (structuredDyadicPrimitive n m tailBits hn htail).generate
      let p : Rat := 1 / (2 : Rat) ^ tailBits
      (∑ key ∈ B.canonicalAcceptedPairReverseLCPKeys,
        finiteAverage (fun seed :
            FiniteBitTape (structuredIndependence m * n) ×
              FiniteBitTape (structuredIndependence m * n) =>
          B.canonicalExactLCPSignedPairCharge (2 * m)
            (D seed.1) (mask seed.2) key)) <=
        p ^ (2 * m) := by
  unfold ResidualModelCountL2Bound
  dsimp only
  rw [residualModelCountDeviationSecondMoment_eq_sum_canonicalExactLCPChargeAverages
    machine n T b m tailBits hn htail rounds]

end MandatoryCanonicalSelectorResidualCount

end

end OneTapeMagnification
end Frontier
end Pnp4
