import Pnp4.Frontier.OneTapeMagnification.FiniteSignedReverseLCPTelescope

namespace Pnp4
namespace Frontier
namespace OneTapeMagnification

/-!
# Terminal-boundary and sibling decomposition of signed reverse-LCP charge

The local reverse-LCP square drop already separates a parent suffix cone from
the squares of its immediate children.  This file refines that identity into
three explicit pieces:

* mass carried by traces which terminate exactly at the current suffix key;
* the cross term between that terminal mass and the child cones;
* ordered cross terms between distinct immediate child cones.

The terminal boundary is also identified semantically with the signed weight
of traces equal to the key.  All identities are finite and unconditional; no
positivity, independence, or rank hypothesis is used.
-/

noncomputable section

open scoped BigOperators

namespace FiniteSignedReverseLCPTerminalBoundary

open FiniteSignedReverseLCPTelescope

/-! ## Exact terminal mass -/

/-- The part of a suffix-cone mass not carried by any immediate child cone. -/
def suffixTerminalBoundaryMass
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) : Rat :=
  suffixConeMass trace weight key -
    (nextSuffixSymbols trace key).sum (fun symbol =>
      suffixConeMass trace weight (symbol :: key))

private theorem longestCommonPrefix_self
    {Alphabet : Type*} [DecidableEq Alphabet] (xs : List Alphabet) :
    FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix xs xs = xs := by
  induction xs with
  | nil => rfl
  | cons head tail ih =>
      simp [FiniteUnambiguousFBDD.ReverseLCP.longestCommonPrefix, ih]

private theorem prefixTerminalWeightedIndicator
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) (index : Index) :
    (if trace index = key then weight index else 0) =
      (if key <+: trace index then weight index else 0) -
        (nextPrefixSymbols trace key).sum (fun symbol =>
          if key ++ [symbol] <+: trace index then weight index else 0) := by
  classical
  have hindicator := exactLCPIndicator_eq_commonPrefix_sub_children
    (trace index) (trace index) key (nextPrefixSymbols trace key)
    (fun symbol hprefix =>
      mem_nextPrefixSymbols_of_isPrefix trace key index symbol hprefix)
  have hindicator' :
      (if trace index = key then (1 : Rat) else 0) =
        (if key <+: trace index then (1 : Rat) else 0) -
          (nextPrefixSymbols trace key).sum (fun symbol =>
            if key ++ [symbol] <+: trace index then (1 : Rat) else 0) := by
    simpa [longestCommonPrefix_self] using hindicator
  calc
    (if trace index = key then weight index else 0) =
        (if trace index = key then (1 : Rat) else 0) * weight index := by
      split <;> simp
    _ = ((if key <+: trace index then (1 : Rat) else 0) -
          (nextPrefixSymbols trace key).sum (fun symbol =>
            if key ++ [symbol] <+: trace index then (1 : Rat) else 0)) *
          weight index := by rw [hindicator']
    _ = _ := by
      rw [sub_mul, Finset.sum_mul]
      simp

/-- Removing all immediate prefix-child cones leaves exactly the signed mass
of traces which terminate at the prefix key. -/
theorem prefixConeMass_sub_children_eq_exactTraceMass
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    prefixConeMass trace weight key -
        (nextPrefixSymbols trace key).sum (fun symbol =>
          prefixConeMass trace weight (key ++ [symbol])) =
      (Finset.univ : Finset Index).sum (fun index =>
        if trace index = key then weight index else 0) := by
  classical
  unfold prefixConeMass
  calc
    (Finset.univ : Finset Index).sum (fun index =>
        if key <+: trace index then weight index else 0) -
        (nextPrefixSymbols trace key).sum (fun symbol =>
          (Finset.univ : Finset Index).sum (fun index =>
            if key ++ [symbol] <+: trace index then weight index else 0)) =
      (Finset.univ : Finset Index).sum (fun index =>
        if key <+: trace index then weight index else 0) -
        (Finset.univ : Finset Index).sum (fun index =>
          (nextPrefixSymbols trace key).sum (fun symbol =>
            if key ++ [symbol] <+: trace index then weight index else 0)) := by
      congr 1
      exact Finset.sum_comm
    _ = (Finset.univ : Finset Index).sum (fun index =>
        (if key <+: trace index then weight index else 0) -
          (nextPrefixSymbols trace key).sum (fun symbol =>
            if key ++ [symbol] <+: trace index then weight index else 0)) := by
      exact Finset.sum_sub_distrib.symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      exact (prefixTerminalWeightedIndicator trace weight key index).symm

/-- The suffix terminal boundary has the intended semantics: it is precisely
the signed mass of traces equal to `key`, rather than an additional analytic
error term. -/
theorem suffixTerminalBoundaryMass_eq_exactTraceMass
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    suffixTerminalBoundaryMass trace weight key =
      (Finset.univ : Finset Index).sum (fun index =>
        if trace index = key then weight index else 0) := by
  classical
  unfold suffixTerminalBoundaryMass nextSuffixSymbols
  rw [suffixConeMass_eq_prefixConeMass_reverse]
  calc
    prefixConeMass (fun index => (trace index).reverse) weight key.reverse -
        (nextPrefixSymbols (fun index => (trace index).reverse) key.reverse).sum
          (fun symbol => suffixConeMass trace weight (symbol :: key)) =
      prefixConeMass (fun index => (trace index).reverse) weight key.reverse -
        (nextPrefixSymbols (fun index => (trace index).reverse) key.reverse).sum
          (fun symbol => prefixConeMass
            (fun index => (trace index).reverse) weight
            (key.reverse ++ [symbol])) := by
      congr 1
      apply Finset.sum_congr rfl
      intro symbol _
      rw [suffixConeMass_eq_prefixConeMass_reverse]
      simp
    _ = (Finset.univ : Finset Index).sum (fun index =>
        if (trace index).reverse = key.reverse then weight index else 0) := by
      exact prefixConeMass_sub_children_eq_exactTraceMass
        (fun index => (trace index).reverse) weight key.reverse
    _ = _ := by
      apply Finset.sum_congr rfl
      intro index _
      simp

/-! ## Ordered sibling expansion -/

/-- The square of a finite sum is the sum of diagonal squares plus all
ordered off-diagonal products, represented by erasing the left index from the
right-index finset. -/
lemma sum_mul_sum_eq_sum_sq_add_erase
    {alpha : Type*} [DecidableEq alpha]
    (s : Finset alpha) (f : alpha -> Rat) :
    (s.sum f) ^ 2 =
      s.sum (fun x => (f x) ^ 2) +
        s.sum (fun x => (s.erase x).sum (fun y => f x * f y)) := by
  rw [pow_two, Finset.sum_mul_sum]
  calc
    s.sum (fun x => s.sum (fun y => f x * f y)) =
        s.sum (fun x => (f x) ^ 2 +
          (s.erase x).sum (fun y => f x * f y)) := by
      apply Finset.sum_congr rfl
      intro x hx
      have hsplit := Finset.sum_erase_add s (fun y => f x * f y) hx
      rw [hsplit.symm]
      ring
    _ = _ := by
      rw [Finset.sum_add_distrib]

/-- Exact local decomposition of one signed reverse-LCP charge into terminal
boundary terms and ordered products of distinct immediate sibling cones. -/
theorem exactLCSPairCharge_eq_terminalBoundary_add_orderedSiblingCross
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet) :
    exactLCSPairCharge trace weight key =
      suffixTerminalBoundaryMass trace weight key ^ 2 +
      2 * suffixTerminalBoundaryMass trace weight key *
        (nextSuffixSymbols trace key).sum (fun symbol =>
          suffixConeMass trace weight (symbol :: key)) +
      (nextSuffixSymbols trace key).sum (fun leftSymbol =>
        ((nextSuffixSymbols trace key).erase leftSymbol).sum
          (fun rightSymbol =>
            suffixConeMass trace weight (leftSymbol :: key) *
              suffixConeMass trace weight (rightSymbol :: key))) := by
  rw [exactLCSPairCharge_eq_suffixConeMass_sq_sub_children]
  let T := suffixTerminalBoundaryMass trace weight key
  let C := fun symbol => suffixConeMass trace weight (symbol :: key)
  let S := (nextSuffixSymbols trace key).sum C
  let Q := (nextSuffixSymbols trace key).sum (fun x => (C x) ^ 2)
  let O := (nextSuffixSymbols trace key).sum (fun x =>
    ((nextSuffixSymbols trace key).erase x).sum (fun y => C x * C y))
  have hparent : suffixConeMass trace weight key = T + S := by
    simp [T, S, C, suffixTerminalBoundaryMass]
  have hsquare : S ^ 2 = Q + O := by
    exact sum_mul_sum_eq_sum_sq_add_erase
      (nextSuffixSymbols trace key) C
  rw [hparent]
  change (T + S) ^ 2 - Q = T ^ 2 + 2 * T * S + O
  nlinarith

/-- For a suffix-free finite trace family, terminal traces and proper child
cones cannot occur at the same key.  Hence the terminal/children cross term
vanishes for arbitrary signed atomic weights. -/
theorem suffixTerminalBoundaryMass_mul_childSum_eq_zero_of_suffix_free
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet)
    (hsuffixFree : ∀ left right : Index,
      trace left <:+ trace right -> trace left = trace right) :
    suffixTerminalBoundaryMass trace weight key *
        (nextSuffixSymbols trace key).sum (fun symbol =>
          suffixConeMass trace weight (symbol :: key)) = 0 := by
  classical
  by_cases hexact : ∃ anchor : Index, trace anchor = key
  · rcases hexact with ⟨anchor, hanchor⟩
    have hchildMass : ∀ symbol : Alphabet,
        suffixConeMass trace weight (symbol :: key) = 0 := by
      intro symbol
      unfold suffixConeMass
      apply Finset.sum_eq_zero
      intro index _
      have hnotSuffix : ¬ (symbol :: key) <:+ trace index := by
        intro hsuffix
        have hkeySuffix : key <:+ trace index :=
          (List.suffix_cons symbol key).trans hsuffix
        have htraceEq : trace index = key :=
          (hsuffixFree anchor index (by simpa [hanchor] using hkeySuffix)).symm.trans
            hanchor
        have hlength := hsuffix.length_le
        rw [htraceEq] at hlength
        simp at hlength
      simp [hnotSuffix]
    have hchildren :
        (nextSuffixSymbols trace key).sum (fun symbol =>
          suffixConeMass trace weight (symbol :: key)) = 0 := by
      apply Finset.sum_eq_zero
      intro symbol _
      exact hchildMass symbol
    rw [hchildren]
    ring
  · rw [suffixTerminalBoundaryMass_eq_exactTraceMass]
    have hterminal :
        (Finset.univ : Finset Index).sum (fun index =>
          if trace index = key then weight index else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro index _
      have hne : trace index ≠ key := fun heq => hexact ⟨index, heq⟩
      simp [hne]
    rw [hterminal]
    ring

/-- On a suffix-free trace family the local charge consists only of the
terminal square and ordered products of distinct sibling cones. -/
theorem exactLCSPairCharge_eq_terminalBoundary_sq_add_orderedSiblingCross_of_suffix_free
    {Index Alphabet : Type*} [Fintype Index] [DecidableEq Alphabet]
    (trace : Index -> List Alphabet) (weight : Index -> Rat)
    (key : List Alphabet)
    (hsuffixFree : ∀ left right : Index,
      trace left <:+ trace right -> trace left = trace right) :
    exactLCSPairCharge trace weight key =
      suffixTerminalBoundaryMass trace weight key ^ 2 +
      (nextSuffixSymbols trace key).sum (fun leftSymbol =>
        ((nextSuffixSymbols trace key).erase leftSymbol).sum
          (fun rightSymbol =>
            suffixConeMass trace weight (leftSymbol :: key) *
              suffixConeMass trace weight (rightSymbol :: key))) := by
  rw [exactLCSPairCharge_eq_terminalBoundary_add_orderedSiblingCross]
  have hzero :=
    suffixTerminalBoundaryMass_mul_childSum_eq_zero_of_suffix_free
      trace weight key hsuffixFree
  have hmixed :
      2 * suffixTerminalBoundaryMass trace weight key *
        (nextSuffixSymbols trace key).sum (fun symbol =>
          suffixConeMass trace weight (symbol :: key)) = 0 := by
    nlinarith
  rw [hmixed]
  ring

end FiniteSignedReverseLCPTerminalBoundary

namespace FiniteUnambiguousFBDD

open FiniteSignedReverseLCPTelescope
open FiniteSignedReverseLCPTerminalBoundary

namespace Walk

/-- The rank at the target of a directed walk is at most the rank at its
source. -/
theorem rank_target_le {n : Nat} {B : FiniteUnambiguousFBDD n}
    {source target : B.Vertex} (walk : B.Walk source target) :
    B.rank target <= B.rank source := by
  induction walk with
  | nil => exact Nat.le_refl _
  | cons edge tail ih =>
      exact Nat.le_of_lt (lt_of_le_of_lt ih (B.rank_lt_of_edge edge))

/-- A directed walk whose source and target coincide is empty.  This is the
walk-level form of acyclicity supplied by the strictly decreasing rank. -/
theorem self_eq_nil {n : Nat} {B : FiniteUnambiguousFBDD n}
    {vertex : B.Vertex} (walk : B.Walk vertex vertex) :
    walk = .nil vertex := by
  cases walk with
  | nil => rfl
  | @cons _ middle _ edge tail =>
      have htail := tail.rank_target_le
      have hedge := B.rank_lt_of_edge edge
      omega

end Walk

/-- Canonical start-to-accept full-step traces are suffix-free.  A suffix
split whose suffix is another complete canonical trace must cut again at
`start`; the remaining start-to-start prefix is empty by acyclicity. -/
theorem canonicalInputLabelledFullTrace_suffix_free
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (left right : B.AcceptedModel)
    (hsuffix : B.canonicalInputLabelledFullTrace left <:+
      B.canonicalInputLabelledFullTrace right) :
    B.canonicalInputLabelledFullTrace left =
      B.canonicalInputLabelledFullTrace right := by
  let leftWalk := B.canonicalAcceptingWalk left
  let rightWalk := B.canonicalAcceptingWalk right
  rcases rightWalk.exists_split_of_isSuffix_inputLabelledFullTrace
      right.1 (B.canonicalInputLabelledFullTrace left)
      (by simpa [rightWalk, canonicalInputLabelledFullTrace] using hsuffix) with
    ⟨vertex, prefixWalk, suffixWalk, hsplit, htrace⟩
  have hsource : B.start = vertex :=
    leftWalk.source_eq_of_inputLabelledFullTrace_eq suffixWalk left.1 right.1
      (by simpa [leftWalk] using htrace.symm)
  subst vertex
  have hprefix := prefixWalk.self_eq_nil
  have hwalk : rightWalk = suffixWalk := by
    rw [hsplit, hprefix]
    rfl
  calc
    B.canonicalInputLabelledFullTrace left =
        suffixWalk.inputLabelledFullTrace right.1 := by
      simpa [leftWalk] using htrace.symm
    _ = B.canonicalInputLabelledFullTrace right := by
      simp only [canonicalInputLabelledFullTrace]
      rw [show B.canonicalAcceptingWalk right = rightWalk by rfl, hwalk]

/-- If every accepting walk reads every input coordinate, its complete
input-labelled trace determines the accepted model. -/
theorem canonicalInputLabelledFullTrace_injective_of_readsAll
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    {left right : B.AcceptedModel}
    (htrace : B.canonicalInputLabelledFullTrace left =
      B.canonicalInputLabelledFullTrace right) :
    left = right := by
  let leftWalk := B.canonicalAcceptingWalk left
  let rightWalk := B.canonicalAcceptingWalk right
  have hwalk : leftWalk = rightWalk :=
    leftWalk.eq_of_inputLabelledFullTrace_eq rightWalk left.1 right.1
      (by simpa [leftWalk, rightWalk] using htrace)
  have hfull :
      leftWalk.inputLabelledFullTrace left.1 =
        leftWalk.inputLabelledFullTrace right.1 := by
    have h := htrace
    change leftWalk.inputLabelledFullTrace left.1 =
      rightWalk.inputLabelledFullTrace right.1 at h
    rw [← hwalk] at h
    exact h
  have hquery :=
    leftWalk.inputLabelledQueryTrace_eq_of_inputLabelledFullTrace_eq
      left.1 right.1 hfull
  apply Subtype.ext
  funext queryIndex
  apply leftWalk.eq_on_queryVars_of_inputLabelledQueryTrace_eq
    left.1 right.1 hquery queryIndex
  rw [hreadsAll leftWalk]
  simp

/-- Canonical residual mass carried by accepted-model traces which terminate
at exactly the current reverse-LCP key. -/
noncomputable def canonicalResidualDeviationTerminalBoundaryMass {n : Nat}
    (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) : Rat :=
  suffixTerminalBoundaryMass B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key

/-- The canonical terminal-boundary alias is the residual-deviation mass of
accepted models whose complete full-step trace equals `key`. -/
theorem canonicalResidualDeviationTerminalBoundaryMass_eq_exactTraceMass
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) :
    B.canonicalResidualDeviationTerminalBoundaryMass cutoff base mask key =
      (Finset.univ : Finset B.AcceptedModel).sum (fun accepted =>
        if B.canonicalInputLabelledFullTrace accepted = key then
          B.acceptedPointResidualDeviation accepted cutoff base mask
        else 0) := by
  exact suffixTerminalBoundaryMass_eq_exactTraceMass
    B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key

/-- Under full-read semantics, a terminal key carries exactly one atomic
residual deviation whenever an accepted model realizes that key. -/
theorem canonicalResidualDeviationTerminalBoundaryMass_eq_accepted_of_readsAll
    {n : Nat} (B : FiniteUnambiguousFBDD n)
    (hreadsAll : ∀ walk : B.Walk B.start B.accept,
      walk.queryVars = Finset.univ)
    (cutoff : Nat) (base mask : Fin n -> Bool)
    (key : List (InputLabelledFullStep B)) (accepted : B.AcceptedModel)
    (hkey : B.canonicalInputLabelledFullTrace accepted = key) :
    B.canonicalResidualDeviationTerminalBoundaryMass cutoff base mask key =
      B.acceptedPointResidualDeviation accepted cutoff base mask := by
  rw [B.canonicalResidualDeviationTerminalBoundaryMass_eq_exactTraceMass]
  classical
  calc
    (Finset.univ : Finset B.AcceptedModel).sum (fun other =>
        if B.canonicalInputLabelledFullTrace other = key then
          B.acceptedPointResidualDeviation other cutoff base mask
        else 0) =
      (if B.canonicalInputLabelledFullTrace accepted = key then
        B.acceptedPointResidualDeviation accepted cutoff base mask
      else 0) := by
        apply Finset.sum_eq_single accepted
        · intro other _ hne
          have htraceNe :
              B.canonicalInputLabelledFullTrace other ≠ key := by
            intro hother
            apply hne
            apply B.canonicalInputLabelledFullTrace_injective_of_readsAll
              hreadsAll
            exact hother.trans hkey.symm
          simp [htraceNe]
        · simp
    _ = B.acceptedPointResidualDeviation accepted cutoff base mask := by
      simp [hkey]

/-- For canonical accepting traces, acyclicity makes the mixed product of
terminal residual mass and proper child-cone residual mass vanish. -/
theorem canonicalResidualDeviationTerminalBoundaryMass_mul_childSum_eq_zero
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) :
    B.canonicalResidualDeviationTerminalBoundaryMass cutoff base mask key *
        (B.canonicalImmediateReverseLCPSteps key).sum (fun step =>
          B.canonicalResidualDeviationSuffixConeMass
            cutoff base mask (step :: key)) = 0 := by
  exact suffixTerminalBoundaryMass_mul_childSum_eq_zero_of_suffix_free
    B.canonicalInputLabelledFullTrace
    (fun accepted =>
      B.acceptedPointResidualDeviation accepted cutoff base mask) key
    (fun left right hsuffix =>
      B.canonicalInputLabelledFullTrace_suffix_free left right hsuffix)

/-- Exact canonical local charge after removing the vanishing
terminal/children cross term: a terminal square plus ordered cross products
of distinct immediate sibling cones. -/
theorem canonicalExactLCPSignedPairCharge_eq_terminalBoundary_sq_add_orderedSiblingCross
    {n : Nat} (B : FiniteUnambiguousFBDD n) (cutoff : Nat)
    (base mask : Fin n -> Bool) (key : List (InputLabelledFullStep B)) :
    B.canonicalExactLCPSignedPairCharge cutoff base mask key =
      B.canonicalResidualDeviationTerminalBoundaryMass
          cutoff base mask key ^ 2 +
        (B.canonicalImmediateReverseLCPSteps key).sum (fun leftStep =>
          ((B.canonicalImmediateReverseLCPSteps key).erase leftStep).sum
            (fun rightStep =>
              B.canonicalResidualDeviationSuffixConeMass
                  cutoff base mask (leftStep :: key) *
                B.canonicalResidualDeviationSuffixConeMass
                  cutoff base mask (rightStep :: key))) := by
  exact
    exactLCSPairCharge_eq_terminalBoundary_sq_add_orderedSiblingCross_of_suffix_free
      B.canonicalInputLabelledFullTrace
      (fun accepted =>
        B.acceptedPointResidualDeviation accepted cutoff base mask) key
      (fun left right hsuffix =>
        B.canonicalInputLabelledFullTrace_suffix_free left right hsuffix)

end FiniteUnambiguousFBDD

end

end OneTapeMagnification
end Frontier
end Pnp4
