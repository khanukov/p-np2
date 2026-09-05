import Pnp4.Frontier.ContractExpansion.ContentTargetSizeBound
import Pnp4.Frontier.ContractExpansion.ContentSemanticVerifier

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-!
# A transparent exponent for the concrete tree-MCSP prefix length

This file keeps every degree used below as data.  In particular, no natural
number is extracted from a proof of `PolyBoundedInTable`.

The intermediate exponents mirror the constructors in
`ExtractedScheduleGrowth.lean`:

* `const c` uses exponent `c`;
* `add` sends `a,b` to `max a b + 1`;
* `mul` sends `a,b` to `a + b`;
* `pow c` sends `a` to `a * c`;
* `of_le` preserves the exponent.

Thus the threshold exponent is `k + 1`, the concrete witness exponent is
`k + 6`, and the five left-associated summands of `treeMCSPPrefixM` give
`max 10 (k + 6) + 2`.  The final conversion is the constructive formula used
by `PolyBoundedInTable.powAdd`, namely `e |-> 2*e + 2^e`.
-/

/-! The next four equations expose the concrete definitions used by the
degree calculation.  They are definitional equations, not asymptotic
surrogates. -/

theorem tableLen_eq_two_pow_explicit (n : Nat) :
    Pnp3.Models.Partial.tableLen n = 2 ^ n := by
  rfl

theorem thresholdPoly_eq_explicit (k n : Nat) :
    thresholdPoly k n = n ^ k + k := by
  rfl

theorem treeCircuitWitnessBits_thresholdPoly_eq_explicit (k n : Nat) :
    (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n =
      (bitLength n + 4) * (n ^ k + k) := by
  rfl

theorem treeMCSPPrefixM_thresholdPoly_eq_explicit (k n : Nat) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n =
      8 + (2 * bitLength (n + 1) - 1) + 2 ^ n +
        bitLength ((bitLength n + 4) * (n ^ k + k)) +
        (bitLength n + 4) * (n ^ k + k) := by
  rfl

/-! ## Fixed-exponent versions of the actual `PolyBoundedInTable` operations -/

/-- A version of `PolyBoundedInTable` whose exponent is explicit data. -/
private def BoundedInTableAt (e : Nat) (f : Nat → Nat) : Prop :=
  ∀ n : Nat,
    f n ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ e

private theorem one_le_tableLen_explicit (n : Nat) :
    1 ≤ Pnp3.Models.Partial.tableLen n :=
  Nat.one_le_two_pow

private theorem boundedInTableAt_of_le
    {e : Nat} {f g : Nat → Nat}
    (hfg : ∀ n, f n ≤ g n)
    (hg : BoundedInTableAt e g) :
    BoundedInTableAt e f := by
  intro n
  exact le_trans (hfg n) (hg n)

/-- Fixed-exponent counterpart of `PolyBoundedInTable.const`. -/
private theorem boundedInTableAt_const (c : Nat) :
    BoundedInTableAt c (fun _ => c) := by
  intro n
  calc
    c ≤ 2 ^ c := Nat.le_of_lt Nat.lt_two_pow_self
    _ ≤ (Pnp3.Models.Partial.tableLen n + 1) ^ c :=
      Nat.pow_le_pow_left (by
        have := one_le_tableLen_explicit n
        omega) c

/-- The exact exponent-one witness used for `polyBoundedInTable_tableLen`. -/
private theorem boundedInTableAt_tableLen :
    BoundedInTableAt 1 (fun n => Pnp3.Models.Partial.tableLen n) := by
  intro n
  rw [pow_one]
  exact Nat.le_succ _

/-- Fixed-exponent counterpart of `PolyBoundedInTable.add`. -/
private theorem boundedInTableAt_add
    {a b : Nat} {f g : Nat → Nat}
    (hf : BoundedInTableAt a f)
    (hg : BoundedInTableAt b g) :
    BoundedInTableAt (max a b + 1) (fun n => f n + g n) := by
  intro n
  have hbase : 2 ≤ Pnp3.Models.Partial.tableLen n + 1 := by
    have := one_le_tableLen_explicit n
    omega
  have hf' : f n ≤
      (Pnp3.Models.Partial.tableLen n + 1) ^ max a b :=
    le_trans (hf n)
      (Nat.pow_le_pow_right (by omega) (le_max_left a b))
  have hg' : g n ≤
      (Pnp3.Models.Partial.tableLen n + 1) ^ max a b :=
    le_trans (hg n)
      (Nat.pow_le_pow_right (by omega) (le_max_right a b))
  calc
    f n + g n ≤
        (Pnp3.Models.Partial.tableLen n + 1) ^ max a b +
          (Pnp3.Models.Partial.tableLen n + 1) ^ max a b := by
            omega
    _ = 2 * (Pnp3.Models.Partial.tableLen n + 1) ^ max a b := by
          ring
    _ ≤ (Pnp3.Models.Partial.tableLen n + 1) *
          (Pnp3.Models.Partial.tableLen n + 1) ^ max a b :=
      Nat.mul_le_mul_right _ hbase
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (max a b + 1) :=
      (pow_succ' _ _).symm

/-- Fixed-exponent counterpart of `PolyBoundedInTable.mul`. -/
private theorem boundedInTableAt_mul
    {a b : Nat} {f g : Nat → Nat}
    (hf : BoundedInTableAt a f)
    (hg : BoundedInTableAt b g) :
    BoundedInTableAt (a + b) (fun n => f n * g n) := by
  intro n
  calc
    f n * g n ≤
        (Pnp3.Models.Partial.tableLen n + 1) ^ a *
          (Pnp3.Models.Partial.tableLen n + 1) ^ b :=
      Nat.mul_le_mul (hf n) (hg n)
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (a + b) :=
      (pow_add _ _ _).symm

/-- Fixed-exponent counterpart of `PolyBoundedInTable.pow`. -/
private theorem boundedInTableAt_pow
    {a : Nat} {f : Nat → Nat}
    (hf : BoundedInTableAt a f) (c : Nat) :
    BoundedInTableAt (a * c) (fun n => (f n) ^ c) := by
  intro n
  calc
    (f n) ^ c ≤
        ((Pnp3.Models.Partial.tableLen n + 1) ^ a) ^ c :=
      Nat.pow_le_pow_left (hf n) c
    _ = (Pnp3.Models.Partial.tableLen n + 1) ^ (a * c) := by
      rw [← pow_mul]

/-! ## Unwinding the concrete threshold, witness, and ambient constructions -/

private def thresholdConstructionExponent (k : Nat) : Nat :=
  max (1 * k) k + 1

private def witnessConstructionExponent (k : Nat) : Nat :=
  (max 1 4 + 1) + thresholdConstructionExponent k

private def gammaConstructionExponent : Nat :=
  2 + 1

/-- The degree obtained by following, without reassociation, the actual term
`((((const tagLen).add gamma).add tableLen).add idxWidth).add witness`. -/
private def ambientConstructionExponent (k : Nat) : Nat :=
  max
    (max
      (max
        (max tagLen gammaConstructionExponent + 1)
        1 + 1)
      (witnessConstructionExponent k) + 1)
    (witnessConstructionExponent k) + 1

/-- A simplified, still fully explicit exponent for the `(tableLen+1)` bound. -/
def treeMCSPPrefixTableExponent (k : Nat) : Nat :=
  max 10 (k + 6) + 2

private theorem thresholdConstructionExponent_eq (k : Nat) :
    thresholdConstructionExponent k = k + 1 := by
  simp [thresholdConstructionExponent]

private theorem witnessConstructionExponent_eq (k : Nat) :
    witnessConstructionExponent k = k + 6 := by
  simp [witnessConstructionExponent, thresholdConstructionExponent]
  omega

private theorem ambientConstructionExponent_eq (k : Nat) :
    ambientConstructionExponent k = treeMCSPPrefixTableExponent k := by
  unfold ambientConstructionExponent
  rw [witnessConstructionExponent_eq k]
  change
    max (max 10 (k + 6) + 1) (k + 6) + 1 =
      max 10 (k + 6) + 2
  have hle : k + 6 ≤ max 10 (k + 6) + 1 :=
    le_trans (le_max_right 10 (k + 6)) (Nat.le_succ _)
  rw [max_eq_left hle]

private theorem boundedInTableAt_id :
    BoundedInTableAt 1 (fun n => n) :=
  boundedInTableAt_of_le
    (fun _ => Nat.le_of_lt Nat.lt_two_pow_self)
    boundedInTableAt_tableLen

private theorem boundedInTableAt_bitLength :
    BoundedInTableAt 1 bitLength :=
  boundedInTableAt_of_le
    (fun n => le_trans (bitLength_le_self n)
      (Nat.le_of_lt Nat.lt_two_pow_self))
    boundedInTableAt_tableLen

/-- This is the explicit-exponent form of the actual construction
`(polyBoundedInTable_id.pow k).add (PolyBoundedInTable.const k)`. -/
private theorem boundedInTableAt_thresholdPoly (k : Nat) :
    BoundedInTableAt (thresholdConstructionExponent k) (thresholdPoly k) := by
  change BoundedInTableAt (thresholdConstructionExponent k)
    (fun n => n ^ k + k)
  exact boundedInTableAt_add
    (boundedInTableAt_pow boundedInTableAt_id k)
    (boundedInTableAt_const k)

/-- This follows the existing gamma proof: first bound by `2*tableLen`, then
use exponents `2` and `1` for the multiplication. -/
private theorem boundedInTableAt_gammaLen :
    BoundedInTableAt gammaConstructionExponent gammaLen := by
  apply boundedInTableAt_of_le (g := fun n =>
    2 * Pnp3.Models.Partial.tableLen n)
  · intro n
    have hb : bitLength (n + 1) ≤ n + 1 :=
      bitLength_le_self (n + 1)
    have ht : n + 1 ≤ Pnp3.Models.Partial.tableLen n :=
      Nat.lt_two_pow_self
    unfold gammaLen
    omega
  · exact boundedInTableAt_mul
      (boundedInTableAt_const 2)
      boundedInTableAt_tableLen

/-- Explicit form of the concrete witness construction
`(bitLength.add (const 4)).mul thresholdPoly`. -/
private theorem boundedInTableAt_treeWitnessBits (k : Nat) :
    BoundedInTableAt (witnessConstructionExponent k)
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits := by
  change BoundedInTableAt (witnessConstructionExponent k)
    (fun n => (bitLength n + 4) * (n ^ k + k))
  exact boundedInTableAt_mul
    (boundedInTableAt_add boundedInTableAt_bitLength
      (boundedInTableAt_const 4))
    (boundedInTableAt_thresholdPoly k)

/-- `idxWidth` uses `bitLength W ≤ W`, so it preserves the witness exponent. -/
private theorem boundedInTableAt_treeIdxWidth (k : Nat) :
    BoundedInTableAt (witnessConstructionExponent k)
      (idxWidth
        (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits) :=
  boundedInTableAt_of_le
    (fun n => bitLength_le_self
      ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n))
    (boundedInTableAt_treeWitnessBits k)

/-- Fixed-degree expansion of
`polyBoundedInTable_treeMCSPPrefixM_of_witnessPoly`.  The order of all four
`add` operations is the order in the source theorem. -/
private theorem boundedInTableAt_treeMCSPPrefixM_construction (k : Nat) :
    BoundedInTableAt (ambientConstructionExponent k)
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k))) := by
  have hTag : BoundedInTableAt tagLen (fun _ => tagLen) :=
    boundedInTableAt_const tagLen
  have hGamma := boundedInTableAt_gammaLen
  have hTable := boundedInTableAt_tableLen
  have hIdx := boundedInTableAt_treeIdxWidth k
  have hWitness := boundedInTableAt_treeWitnessBits k
  have hTagGamma := boundedInTableAt_add hTag hGamma
  have hThroughTable := boundedInTableAt_add hTagGamma hTable
  have hThroughIdx := boundedInTableAt_add hThroughTable hIdx
  have hAll := boundedInTableAt_add hThroughIdx hWitness
  unfold treeMCSPPrefixM
  exact hAll

/-- The complete expanded `(tableLen n + 1)^e` inequality. -/
theorem treeMCSPPrefixM_thresholdPoly_table_explicit (k n : Nat) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n ≤
      (Pnp3.Models.Partial.tableLen n + 1) ^
        treeMCSPPrefixTableExponent k := by
  have h := boundedInTableAt_treeMCSPPrefixM_construction k n
  rw [ambientConstructionExponent_eq k] at h
  exact h

/-- The explicit inequality also gives the original existential interface, with
the witness displayed rather than recovered from a proof. -/
theorem polyBoundedInTable_treeMCSPPrefixM_thresholdPoly_explicit (k : Nat) :
    PolyBoundedInTable
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k))) :=
  ⟨treeMCSPPrefixTableExponent k,
    treeMCSPPrefixM_thresholdPoly_table_explicit k⟩

/-! ## Constructive conversion to the `N^d+d` convention -/

/-- The formula returned by the source implementation of
`PolyBoundedInTable.powAdd`, now applied to a visible exponent. -/
def treeMCSPPrefixPowAddExponent (k : Nat) : Nat :=
  2 * treeMCSPPrefixTableExponent k +
    2 ^ treeMCSPPrefixTableExponent k

/-- The `N=0` branch of the all-base arithmetic conversion. -/
private theorem powAddNormalize_zero (e : Nat) :
    (0 + 1) ^ e ≤
      0 ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) := by
  have hpos : 0 < 2 * e + 2 ^ e := by
    have := Nat.two_pow_pos e
    omega
  have hone : 1 ≤ 2 * e + 2 ^ e :=
    Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hpos)
  calc
    (0 + 1) ^ e = 1 := by simp
    _ ≤ 2 * e + 2 ^ e := hone
    _ ≤ 0 ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) :=
      Nat.le_add_left _ _

/-- The `N=1` branch of the all-base arithmetic conversion. -/
private theorem powAddNormalize_one (e : Nat) :
    (1 + 1) ^ e ≤
      1 ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) := by
  calc
    (1 + 1) ^ e = 2 ^ e := by simp
    _ ≤ 2 * e + 2 ^ e := Nat.le_add_left _ _
    _ ≤ 1 ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) :=
      Nat.le_add_left _ _

/-- Constructive all-base normalizer.  Unlike the private helper behind the
source `powAdd`, this statement includes and visibly discharges `N=0` and
`N=1`. -/
theorem powAddNormalize_allBases (N e : Nat) :
    (N + 1) ^ e ≤
      N ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) := by
  by_cases hzero : N = 0
  · subst N
    exact powAddNormalize_zero e
  by_cases hone : N = 1
  · subst N
    exact powAddNormalize_one e
  have htwo : 2 ≤ N := by omega
  have hpow : 2 ^ e ≤ N ^ e :=
    Nat.pow_le_pow_left htwo e
  have honeN : 1 ≤ N := by omega
  have hmono : N ^ (2 * e) ≤ N ^ (2 * e + 2 ^ e) :=
    Nat.pow_le_pow_right honeN
      (Nat.le_add_right (2 * e) (2 ^ e))
  calc
    (N + 1) ^ e ≤ (2 * N) ^ e :=
      Nat.pow_le_pow_left (by omega) e
    _ = 2 ^ e * N ^ e := by rw [mul_pow]
    _ ≤ N ^ e * N ^ e := Nat.mul_le_mul hpow (le_refl _)
    _ = N ^ (2 * e) := by rw [← pow_add, two_mul]
    _ ≤ N ^ (2 * e + 2 ^ e) := hmono
    _ ≤ N ^ (2 * e + 2 ^ e) + (2 * e + 2 ^ e) :=
      Nat.le_add_right _ _

/-- Required explicit `powAdd` bound for the concrete polynomial-threshold
prefix convention. -/
theorem treeMCSPPrefixM_thresholdPoly_powAdd_explicit (k n : Nat) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n ≤
      Pnp3.Models.Partial.tableLen n ^
          treeMCSPPrefixPowAddExponent k +
        treeMCSPPrefixPowAddExponent k := by
  calc
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n ≤
        (Pnp3.Models.Partial.tableLen n + 1) ^
          treeMCSPPrefixTableExponent k :=
      treeMCSPPrefixM_thresholdPoly_table_explicit k n
    _ ≤ Pnp3.Models.Partial.tableLen n ^
          treeMCSPPrefixPowAddExponent k +
        treeMCSPPrefixPowAddExponent k := by
      simpa [treeMCSPPrefixPowAddExponent] using
        powAddNormalize_allBases (Pnp3.Models.Partial.tableLen n)
          (treeMCSPPrefixTableExponent k)

/-! ## Choice-free FEAS transformation and Boolean-verifier corollaries -/

/-- The final content-size exponent.  The extra successor is the same one used
by the existing FEAS argument to cover both the wide and narrow cases. -/
def contentCapExponent (k : Nat) : Nat :=
  treeMCSPPrefixPowAddExponent k + 1

/-- Choice-free FEAS transformer.  Its degree is an explicit argument and its
only growth premise is the displayed pointwise `tableLen^d+d` inequality. -/
theorem contentSemanticAccepts_header_target_of_powAdd
    (k d : Nat)
    (hgrowth : ∀ r : Nat,
      treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r ≤
        Pnp3.Models.Partial.tableLen r ^ d + d)
    {N : Nat} (z : PrefixBitVec N) (n_header consumed : Nat)
    (hheader : contentHeader? z = some (n_header, consumed))
    (hsemantic :
      contentSemanticAccepts
        (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n_header ≤
      N ^ (d + 1) + (d + 1) := by
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  change contentSemanticAccepts codec z = true at hsemantic
  have haccepts : ContentAccepts codec z :=
    (contentSemanticAccepts_eq_true_iff codec z).mp hsemantic
  by_cases hwide : N < treeMCSPPrefixM codec n_header
  · obtain ⟨pr, hpr, htable⟩ :=
      contentAccepts_parsed_tableLen_le_of_header_target_wide
        k z n_header consumed hheader haccepts hwide
    have hlength :
        treeMCSPPrefixM codec n_header =
          treeMCSPPrefixM codec pr.2.n :=
      contentInput?_target_length codec z n_header consumed hheader hpr
    have htablePos : 0 < Pnp3.Models.Partial.tableLen pr.2.n := by
      simp [Pnp3.Models.Partial.tableLen]
    have hNpos : 0 < N := lt_of_lt_of_le htablePos htable
    calc
      treeMCSPPrefixM codec n_header =
          treeMCSPPrefixM codec pr.2.n := hlength
      _ ≤ Pnp3.Models.Partial.tableLen pr.2.n ^ d + d :=
        hgrowth pr.2.n
      _ ≤ N ^ d + d :=
        Nat.add_le_add_right (Nat.pow_le_pow_left htable d) d
      _ ≤ N ^ (d + 1) + (d + 1) := by
        apply Nat.add_le_add
        · exact Nat.pow_le_pow_right
            (Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt hNpos))
            (Nat.le_succ d)
        · omega
  · have hnarrow : treeMCSPPrefixM codec n_header ≤ N := by omega
    have hNpow : N ≤ N ^ (d + 1) := Nat.le_pow (by omega)
    exact le_trans hnarrow
      (le_trans hNpow (Nat.le_add_right _ _))

/-- Instantiation of the choice-free transformer at the transparent exponent. -/
theorem contentSemanticAccepts_header_target_explicit
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (n_header consumed : Nat)
    (hheader : contentHeader? z = some (n_header, consumed))
    (hsemantic :
      contentSemanticAccepts
        (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n_header ≤
      N ^ contentCapExponent k + contentCapExponent k := by
  simpa [contentCapExponent] using
    contentSemanticAccepts_header_target_of_powAdd
      k (treeMCSPPrefixPowAddExponent k)
      (treeMCSPPrefixM_thresholdPoly_powAdd_explicit k)
      z n_header consumed hheader hsemantic

/-- The cap for the actual dependent target carried by a successful
`contentInput?`, rather than merely for the header target. -/
theorem contentSemanticAccepts_successful_input_target_explicit
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    {pr : Σ r : Nat, PrefixInput
      (treeMCSPSearchProblem (thresholdPoly k)
        (TreeMCSPSearchWitnessEncoding.ofCodec
          (treeCircuitWitnessCodec (thresholdPoly k))))
      (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r)}
    (hinput :
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr)
    (hsemantic :
      contentSemanticAccepts
        (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n ≤
      N ^ contentCapExponent k + contentCapExponent k := by
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  change contentInput? codec z = some pr at hinput
  change contentSemanticAccepts codec z = true at hsemantic
  cases hheader : contentHeader? z with
  | none =>
      unfold contentInput? at hinput
      rw [hheader] at hinput
      simp at hinput
  | some header =>
      rcases header with ⟨n_header, consumed⟩
      have hlength :
          treeMCSPPrefixM codec n_header =
            treeMCSPPrefixM codec pr.2.n :=
        contentInput?_target_length codec z n_header consumed hheader hinput
      have hbound := contentSemanticAccepts_header_target_explicit
        k z n_header consumed hheader hsemantic
      rw [← hlength]
      exact hbound

/-- Existential presentation showing that a successful Boolean verification
really supplies a parsed target satisfying the explicit cap. -/
theorem contentSemanticAccepts_has_bounded_input_target_explicit
    (k : Nat) {N : Nat} (z : PrefixBitVec N)
    (hsemantic :
      contentSemanticAccepts
        (treeCircuitWitnessCodec (thresholdPoly k)) z = true) :
    ∃ pr : Σ r : Nat, PrefixInput
        (treeMCSPSearchProblem (thresholdPoly k)
          (TreeMCSPSearchWitnessEncoding.ofCodec
            (treeCircuitWitnessCodec (thresholdPoly k))))
        (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) r),
      contentInput? (treeCircuitWitnessCodec (thresholdPoly k)) z = some pr ∧
      treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) pr.2.n ≤
        N ^ contentCapExponent k + contentCapExponent k := by
  have haccepts :
      ContentAccepts (treeCircuitWitnessCodec (thresholdPoly k)) z :=
    (contentSemanticAccepts_eq_true_iff
      (treeCircuitWitnessCodec (thresholdPoly k)) z).mp hsemantic
  rcases haccepts with ⟨pr, hinput, _hprefix, _hverifies⟩
  exact ⟨pr, hinput,
    contentSemanticAccepts_successful_input_target_explicit
      k z hinput hsemantic⟩

end ContractExpansion
end Frontier
end Pnp4
