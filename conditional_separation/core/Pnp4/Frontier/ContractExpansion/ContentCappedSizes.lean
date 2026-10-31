import Pnp4.Frontier.ContractExpansion.ContentCappedArithmetic
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Exact capped size records for authoritative content parsing

This module builds concrete threshold, table, witness, gamma, index, and ambient
sizes using `ContentCappedArithmetic`. Success returns every exact field and its
cap proof; failure is exactly strict overflow of the authoritative convention
length. No semantic verifier, machine, or runtime theorem is introduced.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

private theorem option_bind_eq_some_iff
    {alpha beta : Type} (x : Option alpha) (f : alpha → Option beta) (y : beta) :
    x.bind f = some y ↔ ∃ z, x = some z ∧ f z = some y := by
  cases x <;> simp
private theorem option_eq_none_iff_of_some_iff
    (f : Option Nat) (x B : Nat)
    (h : ∀ y, f = some y ↔ y = x ∧ x ≤ B) :
    f = none ↔ B < x := by
  constructor
  · intro hnone
    by_contra hnot
    have hcap : x ≤ B := Nat.le_of_not_gt hnot
    have hsome := (h x).mpr ⟨rfl, hcap⟩
    rw [hnone] at hsome
    contradiction
  · intro hover
    cases hrun : f with
    | none => rfl
    | some y =>
        have hspec := (h y).mp hrun
        exact False.elim ((Nat.not_le_of_lt hover) hspec.2)
/-! ## Exact capped concrete fields -/
/-- `thresholdPoly k n`, computed without constructing an overflowing power. -/
def checkedThresholdPoly (B k n : Nat) : Option Nat :=
  Option.bind (checkedPow B n k) fun p =>
    checkedAdd B p k
@[simp] theorem checkedThresholdPoly_eq_some_iff (B k n t : Nat) :
    checkedThresholdPoly B k n = some t ↔
      t = thresholdPoly k n ∧ thresholdPoly k n ≤ B := by
  unfold checkedThresholdPoly
  rw [option_bind_eq_some_iff]
  constructor
  · rintro ⟨p, hp, ht⟩
    rcases (checkedPow_eq_some_iff B n k p).mp hp with ⟨rfl, hpCap⟩
    rcases (checkedAdd_eq_some_iff B (n ^ k) k t).mp ht with
      ⟨rfl, htCap⟩
    simpa [thresholdPoly] using
      (show n ^ k + k = n ^ k + k ∧ n ^ k + k ≤ B from ⟨rfl, htCap⟩)
  · rintro ⟨rfl, htCap⟩
    have hsumCap : n ^ k + k ≤ B := by
      simpa [thresholdPoly] using htCap
    have hpCap : n ^ k ≤ B := by
      omega
    refine ⟨n ^ k, (checkedPow_eq_some_iff B n k (n ^ k)).mpr
      ⟨rfl, hpCap⟩, ?_⟩
    apply (checkedAdd_eq_some_iff B (n ^ k) k (thresholdPoly k n)).mpr
    exact ⟨rfl, hsumCap⟩
@[simp] theorem checkedThresholdPoly_eq_none_iff (B k n : Nat) :
    checkedThresholdPoly B k n = none ↔ B < thresholdPoly k n :=
  option_eq_none_iff_of_some_iff
    (checkedThresholdPoly B k n) (thresholdPoly k n) B
    (checkedThresholdPoly_eq_some_iff B k n)
/-- `tableLen n = 2^n`, using the same binary checked power. -/
def checkedTableLen (B n : Nat) : Option Nat :=
  checkedPow B 2 n
@[simp] theorem checkedTableLen_eq_some_iff (B n t : Nat) :
    checkedTableLen B n = some t ↔
      t = Pnp3.Models.Partial.tableLen n ∧
        Pnp3.Models.Partial.tableLen n ≤ B := by
  change checkedPow B 2 n = some t ↔
    t = 2 ^ n ∧ 2 ^ n ≤ B
  exact checkedPow_eq_some_iff B 2 n t
@[simp] theorem checkedTableLen_eq_none_iff (B n : Nat) :
    checkedTableLen B n = none ↔
      B < Pnp3.Models.Partial.tableLen n := by
  change checkedPow B 2 n = none ↔ B < 2 ^ n
  exact checkedPow_eq_none_iff B 2 n
private theorem thresholdPoly_pos (k n : Nat) : 0 < thresholdPoly k n := by
  unfold thresholdPoly
  by_cases hk : k = 0
  · subst k
    simp
  · have hkpos : 0 < k := Nat.pos_of_ne_zero hk
    omega
/-- Concrete witness width, retaining only cap-bounded intermediates. -/
def checkedTreeWitnessBits (B k n : Nat) : Option Nat :=
  Option.bind (checkedBitLength B n) fun nBits =>
  Option.bind (checkedAdd B nBits 4) fun factor =>
  Option.bind (checkedThresholdPoly B k n) fun threshold =>
    checkedMul B factor threshold
@[simp] theorem checkedTreeWitnessBits_eq_some_iff
    (B k n W : Nat) :
    checkedTreeWitnessBits B k n = some W ↔
      W = (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n ∧
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n ≤ B := by
  unfold checkedTreeWitnessBits
  simp only [option_bind_eq_some_iff]
  constructor
  · rintro ⟨nBits, hnBits, factor, hfactor, threshold, hthreshold, hW⟩
    rcases (checkedBitLength_eq_some_iff B n nBits).mp hnBits with
      ⟨rfl, hnBitsCap⟩
    rcases (checkedAdd_eq_some_iff B (bitLength n) 4 factor).mp hfactor with
      ⟨rfl, hfactorCap⟩
    rcases (checkedThresholdPoly_eq_some_iff B k n threshold).mp hthreshold with
      ⟨rfl, hthresholdCap⟩
    rcases (checkedMul_eq_some_iff B (bitLength n + 4)
      (thresholdPoly k n) W).mp hW with ⟨rfl, hWCap⟩
    change
      (bitLength n + 4) * thresholdPoly k n =
          (bitLength n + 4) * thresholdPoly k n ∧
        (bitLength n + 4) * thresholdPoly k n ≤ B
    exact ⟨rfl, hWCap⟩
  · rintro ⟨rfl, hWCap⟩
    change (bitLength n + 4) * thresholdPoly k n ≤ B at hWCap
    have hthresholdOne : 1 ≤ thresholdPoly k n :=
      Nat.one_le_iff_ne_zero.mpr (Nat.ne_of_gt (thresholdPoly_pos k n))
    have hfactorOne : 1 ≤ bitLength n + 4 := by omega
    have hfactorW : bitLength n + 4 ≤
        (bitLength n + 4) * thresholdPoly k n := by
      calc
        bitLength n + 4 = (bitLength n + 4) * 1 := by simp
        _ ≤ (bitLength n + 4) * thresholdPoly k n :=
          Nat.mul_le_mul_left _ hthresholdOne
    have hthresholdW : thresholdPoly k n ≤
        (bitLength n + 4) * thresholdPoly k n := by
      calc
        thresholdPoly k n = 1 * thresholdPoly k n := by simp
        _ ≤ (bitLength n + 4) * thresholdPoly k n :=
          Nat.mul_le_mul_right _ hfactorOne
    have hfactorCap : bitLength n + 4 ≤ B :=
      le_trans hfactorW hWCap
    have hnBitsCap : bitLength n ≤ B := by omega
    have hthresholdCap : thresholdPoly k n ≤ B :=
      le_trans hthresholdW hWCap
    refine ⟨bitLength n,
      (checkedBitLength_eq_some_iff B n (bitLength n)).mpr
        ⟨rfl, hnBitsCap⟩,
      bitLength n + 4,
      (checkedAdd_eq_some_iff B (bitLength n) 4 (bitLength n + 4)).mpr
        ⟨rfl, hfactorCap⟩,
      thresholdPoly k n,
      (checkedThresholdPoly_eq_some_iff B k n (thresholdPoly k n)).mpr
        ⟨rfl, hthresholdCap⟩, ?_⟩
    apply (checkedMul_eq_some_iff B (bitLength n + 4)
      (thresholdPoly k n)
      ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)).mpr
    change
      (bitLength n + 4) * thresholdPoly k n =
          (bitLength n + 4) * thresholdPoly k n ∧
        (bitLength n + 4) * thresholdPoly k n ≤ B
    exact ⟨rfl, hWCap⟩
@[simp] theorem checkedTreeWitnessBits_eq_none_iff (B k n : Nat) :
    checkedTreeWitnessBits B k n = none ↔
      B < (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n :=
  option_eq_none_iff_of_some_iff
    (checkedTreeWitnessBits B k n)
    ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) B
    (checkedTreeWitnessBits_eq_some_iff B k n)
/-- Intermediates of the exact gamma-length construction. -/
structure CheckedGammaSizes where
  nSuccBits : Nat
  twicePred : Nat
  gamma : Nat
deriving Repr, DecidableEq
/-- Specification-only canonical gamma intermediates. -/
def exactGammaSizes (n : Nat) : CheckedGammaSizes where
  nSuccBits := bitLength (n + 1)
  twicePred := 2 * (bitLength (n + 1) - 1)
  gamma := gammaLen n
/--
Compute gamma length as `2 * (bitLength (n+1)-1) + 1`.  Computing `2*l`
and then subtracting one would incorrectly reject at the exact cap.
-/
def checkedGammaSizes (B n : Nat) : Option CheckedGammaSizes :=
  Option.bind (checkedBitLength B (n + 1)) fun width =>
  Option.bind (checkedMul B 2 (width - 1)) fun twice =>
  Option.bind (checkedAdd B twice 1) fun result =>
    some { nSuccBits := width, twicePred := twice, gamma := result }
private theorem bitLength_succ_le_gammaLen (n : Nat) :
    bitLength (n + 1) ≤ gammaLen n := by
  rw [gammaLen_eq_two_mul_zeros_add_one]
  have hpos : 0 < bitLength (n + 1) :=
    bitLength_pos_of_pos (Nat.succ_pos n)
  omega
@[simp] theorem checkedGammaSizes_eq_some_iff
    (B n : Nat) (g : CheckedGammaSizes) :
    checkedGammaSizes B n = some g ↔
      g = exactGammaSizes n ∧ gammaLen n ≤ B := by
  unfold checkedGammaSizes
  simp only [option_bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨width, hwidth, twice, htwice, result, hresult, rfl⟩
    rcases (checkedBitLength_eq_some_iff B (n + 1) width).mp hwidth with
      ⟨rfl, hwidthCap⟩
    rcases (checkedMul_eq_some_iff B 2
      (bitLength (n + 1) - 1) twice).mp htwice with
      ⟨rfl, htwiceCap⟩
    rcases (checkedAdd_eq_some_iff B
      (2 * (bitLength (n + 1) - 1)) 1 result).mp hresult with
      ⟨rfl, hresultCap⟩
    constructor
    · unfold exactGammaSizes
      rw [gammaLen_eq_two_mul_zeros_add_one]
    · simpa [gammaLen_eq_two_mul_zeros_add_one] using hresultCap
  · rintro ⟨rfl, hgammaCap⟩
    have hwidthCap : bitLength (n + 1) ≤ B :=
      le_trans (bitLength_succ_le_gammaLen n) hgammaCap
    have htwiceCap : 2 * (bitLength (n + 1) - 1) ≤ B := by
      rw [gammaLen_eq_two_mul_zeros_add_one] at hgammaCap
      omega
    refine ⟨bitLength (n + 1),
      (checkedBitLength_eq_some_iff B (n + 1) (bitLength (n + 1))).mpr
        ⟨rfl, hwidthCap⟩,
      2 * (bitLength (n + 1) - 1),
      (checkedMul_eq_some_iff B 2 (bitLength (n + 1) - 1)
        (2 * (bitLength (n + 1) - 1))).mpr
        ⟨rfl, htwiceCap⟩,
      gammaLen n, ?_, ?_⟩
    · apply (checkedAdd_eq_some_iff B
        (2 * (bitLength (n + 1) - 1)) 1 (gammaLen n)).mpr
      constructor
      · exact (gammaLen_eq_two_mul_zeros_add_one n).symm
      · exact hgammaCap
    · rfl

/-- Record-valued gamma computation fails exactly at strict gamma overflow. -/
@[simp] theorem checkedGammaSizes_eq_none_iff (B n : Nat) :
    checkedGammaSizes B n = none ↔ B < gammaLen n := by
  constructor
  · intro hnone
    by_contra hnot
    have hcap : gammaLen n ≤ B := Nat.le_of_not_gt hnot
    have hsome := (checkedGammaSizes_eq_some_iff B n
      (exactGammaSizes n)).mpr ⟨rfl, hcap⟩
    rw [hnone] at hsome
    contradiction
  · intro hover
    cases hrun : checkedGammaSizes B n with
    | none => rfl
    | some g =>
        have hspec := (checkedGammaSizes_eq_some_iff B n g).mp hrun
        exact False.elim ((Nat.not_le_of_lt hover) hspec.2)

/-- Gamma length alone, with the same exact capped computation. -/
def checkedGammaLen (B n : Nat) : Option Nat :=
  Option.bind (checkedGammaSizes B n) fun g =>
    some g.gamma
@[simp] theorem checkedGammaLen_eq_some_iff (B n g : Nat) :
    checkedGammaLen B n = some g ↔ g = gammaLen n ∧ gammaLen n ≤ B := by
  unfold checkedGammaLen
  rw [option_bind_eq_some_iff]
  constructor
  · rintro ⟨sizes, hsizes, hvalue⟩
    rcases (checkedGammaSizes_eq_some_iff B n sizes).mp hsizes with
      ⟨rfl, hcap⟩
    have hg : g = gammaLen n := by
      simpa [exactGammaSizes, eq_comm] using hvalue
    exact ⟨hg, hcap⟩
  · rintro ⟨rfl, hcap⟩
    refine ⟨exactGammaSizes n,
      (checkedGammaSizes_eq_some_iff B n (exactGammaSizes n)).mpr
        ⟨rfl, hcap⟩, ?_⟩
    simp [exactGammaSizes]
@[simp] theorem checkedGammaLen_eq_none_iff (B n : Nat) :
    checkedGammaLen B n = none ↔ B < gammaLen n :=
  option_eq_none_iff_of_some_iff
    (checkedGammaLen B n) (gammaLen n) B
    (checkedGammaLen_eq_some_iff B n)
/-- Checked width of the active-prefix index field. -/
def checkedIndexWidth (B witnessBits : Nat) : Option Nat :=
  checkedBitLength B witnessBits
@[simp] theorem checkedIndexWidth_eq_some_iff (B W i : Nat) :
    checkedIndexWidth B W = some i ↔
      i = bitLength W ∧ bitLength W ≤ B := by
  simp [checkedIndexWidth]
@[simp] theorem checkedIndexWidth_eq_none_iff (B W : Nat) :
    checkedIndexWidth B W = none ↔ B < bitLength W := by
  simp [checkedIndexWidth]
/-! ## The complete concrete size record -/
/--
Every exact field and every left-associated partial ambient sum used by the
concrete content parser.  All fields are plain naturals; no codec, parser, or
content provider is hidden in this record.
-/
structure ContentSizes where
  powNK : Nat
  threshold : Nat
  nBits : Nat
  witnessFactor : Nat
  tableLen : Nat
  witnessBits : Nat
  gammaBits : Nat
  gammaTwicePred : Nat
  gammaLen : Nat
  indexWidth : Nat
  tagGammaLen : Nat
  throughTableLen : Nat
  throughIndexLen : Nat
  M : Nat
deriving Repr, DecidableEq
/-- Specification-only canonical record.  Executable code does not call it. -/
def exactContentSizes (k n : Nat) : ContentSizes :=
  let codec := treeCircuitWitnessCodec (thresholdPoly k)
  let W := codec.witnessBits n
  let gamma := _root_.Pnp4.Frontier.ContractExpansion.gammaLen n
  let index := idxWidth codec.witnessBits n
  {
    powNK := n ^ k
    threshold := thresholdPoly k n
    nBits := bitLength n
    witnessFactor := bitLength n + 4
    tableLen := Pnp3.Models.Partial.tableLen n
    witnessBits := W
    gammaBits := bitLength (n + 1)
    gammaTwicePred := 2 * (bitLength (n + 1) - 1)
    gammaLen := gamma
    indexWidth := index
    tagGammaLen := tagLen + gamma
    throughTableLen := tagLen + gamma + Pnp3.Models.Partial.tableLen n
    throughIndexLen :=
      tagLen + gamma + Pnp3.Models.Partial.tableLen n + index
    M := treeMCSPPrefixM codec n
  }
/-- One explicit repository equality for every result field. -/
structure ContentSizes.Exact (s : ContentSizes) (k n : Nat) : Prop where
  powNK_eq : s.powNK = n ^ k
  threshold_eq : s.threshold = thresholdPoly k n
  nBits_eq : s.nBits = bitLength n
  witnessFactor_eq : s.witnessFactor = bitLength n + 4
  tableLen_eq : s.tableLen = Pnp3.Models.Partial.tableLen n
  witnessBits_eq :
    s.witnessBits = (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n
  gammaBits_eq : s.gammaBits = bitLength (n + 1)
  gammaTwicePred_eq :
    s.gammaTwicePred = 2 * (bitLength (n + 1) - 1)
  gammaLen_eq :
    s.gammaLen = _root_.Pnp4.Frontier.ContractExpansion.gammaLen n
  indexWidth_eq :
    s.indexWidth = idxWidth
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n
  tagGammaLen_eq :
    s.tagGammaLen = tagLen +
      _root_.Pnp4.Frontier.ContractExpansion.gammaLen n
  throughTableLen_eq :
    s.throughTableLen = tagLen +
      _root_.Pnp4.Frontier.ContractExpansion.gammaLen n +
      Pnp3.Models.Partial.tableLen n
  throughIndexLen_eq :
    s.throughIndexLen = tagLen +
      _root_.Pnp4.Frontier.ContractExpansion.gammaLen n +
      Pnp3.Models.Partial.tableLen n +
      idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n
  M_eq :
    s.M = treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n
theorem exactContentSizes_exact (k n : Nat) :
    (exactContentSizes k n).Exact k n := by
  constructor <;> rfl
theorem ContentSizes.Exact.eq_exactContentSizes
    {s : ContentSizes} {k n : Nat} (h : s.Exact k n) :
    s = exactContentSizes k n := by
  cases s
  cases h
  simp_all [exactContentSizes]
theorem ContentSizes.Exact.witnessBits_le_M
    {s : ContentSizes} {k n : Nat} (h : s.Exact k n) :
    s.witnessBits ≤ s.M := by
  rw [h.witnessBits_eq, h.M_eq]
  unfold treeMCSPPrefixM
  omega
theorem ContentSizes.Exact.tableLen_le_M
    {s : ContentSizes} {k n : Nat} (h : s.Exact k n) :
    s.tableLen ≤ s.M := by
  calc
    s.tableLen = Pnp3.Models.Partial.tableLen n := h.tableLen_eq
    _ ≤ treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n :=
      tableLen_le_treeMCSPPrefixM _ _
    _ = s.M := h.M_eq.symm
private theorem threshold_le_concrete_witnessBits (k n : Nat) :
    thresholdPoly k n ≤
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n := by
  change n ^ k + k ≤ (bitLength n + 4) * (n ^ k + k)
  have hfactor : 1 ≤ bitLength n + 4 := by omega
  calc
    n ^ k + k = 1 * (n ^ k + k) := by simp
    _ ≤ (bitLength n + 4) * (n ^ k + k) :=
      Nat.mul_le_mul_right _ hfactor
private theorem bitLength_le_concrete_witnessBits (k n : Nat) :
    bitLength n ≤
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n := by
  change bitLength n ≤ (bitLength n + 4) * (n ^ k + k)
  have hthreshold : 1 ≤ n ^ k + k := by
    simpa [thresholdPoly] using
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (thresholdPoly_pos k n)))
  calc
    bitLength n ≤ bitLength n + 4 := by omega
    _ = (bitLength n + 4) * 1 := by simp
    _ ≤ (bitLength n + 4) * (n ^ k + k) :=
      Nat.mul_le_mul_left _ hthreshold
private theorem witnessFactor_le_concrete_witnessBits (k n : Nat) :
    bitLength n + 4 ≤
      (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n := by
  change bitLength n + 4 ≤ (bitLength n + 4) * (n ^ k + k)
  have hthreshold : 1 ≤ n ^ k + k := by
    simpa [thresholdPoly] using
      (Nat.one_le_iff_ne_zero.mpr
        (Nat.ne_of_gt (thresholdPoly_pos k n)))
  simpa using Nat.mul_le_mul_left (bitLength n + 4) hthreshold
/--
The executable pipeline.  Every potentially large constructor is behind a
successful cap check, and the final additions follow the repository's exact
left association.
-/
def computeContentSizesCapped (k B n : Nat) : Option ContentSizes :=
  Option.bind (checkedPow B n k) fun powNK =>
  Option.bind (checkedAdd B powNK k) fun threshold =>
  Option.bind (checkedBitLength B n) fun nBits =>
  Option.bind (checkedAdd B nBits 4) fun witnessFactor =>
  Option.bind (checkedMul B witnessFactor threshold) fun witness =>
  Option.bind (checkedTableLen B n) fun table =>
  Option.bind (checkedGammaSizes B n) fun gamma =>
  Option.bind (checkedIndexWidth B witness) fun index =>
  Option.bind (checkedAdd B tagLen gamma.gamma) fun tagGamma =>
  Option.bind (checkedAdd B tagGamma table) fun throughTable =>
  Option.bind (checkedAdd B throughTable index) fun throughIndex =>
  Option.bind (checkedAdd B throughIndex witness) fun total =>
  some {
    powNK := powNK
    threshold := threshold
    nBits := nBits
    witnessFactor := witnessFactor
    tableLen := table
    witnessBits := witness
    gammaBits := gamma.nSuccBits
    gammaTwicePred := gamma.twicePred
    gammaLen := gamma.gamma
    indexWidth := index
    tagGammaLen := tagGamma
    throughTableLen := throughTable
    throughIndexLen := throughIndex
    M := total
  }
/-- Exact success characterization, including every field and the cap. -/
theorem computeContentSizesCapped_eq_some_iff
    (k B n : Nat) (s : ContentSizes) :
    computeContentSizesCapped k B n = some s ↔
      s.Exact k n ∧ s.M ≤ B := by
  unfold computeContentSizesCapped
  simp only [option_bind_eq_some_iff, Option.some.injEq]
  constructor
  · rintro ⟨powNK, hpowNK, threshold, hthreshold, nBits, hnBits,
      witnessFactor, hwitnessFactor, witness, hwitness, table, htable,
      gamma, hgamma, index, hindex, tagGamma, htagGamma,
      throughTable, hthroughTable, throughIndex, hthroughIndex,
      total, htotal, hrecord⟩
    rcases (checkedPow_eq_some_iff B n k powNK).mp hpowNK with
      ⟨rfl, hpowNKCap⟩
    rcases (checkedAdd_eq_some_iff B (n ^ k) k threshold).mp hthreshold with
      ⟨rfl, hthresholdCap⟩
    rcases (checkedBitLength_eq_some_iff B n nBits).mp hnBits with
      ⟨rfl, hnBitsCap⟩
    rcases (checkedAdd_eq_some_iff B (bitLength n) 4 witnessFactor).mp
      hwitnessFactor with ⟨rfl, hwitnessFactorCap⟩
    rcases (checkedMul_eq_some_iff B (bitLength n + 4)
      (n ^ k + k) witness).mp hwitness with ⟨rfl, hwitnessCap⟩
    rcases (checkedTableLen_eq_some_iff B n table).mp htable with
      ⟨rfl, htableCap⟩
    rcases (checkedGammaSizes_eq_some_iff B n gamma).mp hgamma with
      ⟨rfl, hgammaCap⟩
    rcases (checkedIndexWidth_eq_some_iff B
      ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) index).mp
        hindex with ⟨rfl, hindexCap⟩
    rcases (checkedAdd_eq_some_iff B tagLen (gammaLen n) tagGamma).mp
      htagGamma with ⟨rfl, htagGammaCap⟩
    rcases (checkedAdd_eq_some_iff B (tagLen + gammaLen n)
      (Pnp3.Models.Partial.tableLen n) throughTable).mp hthroughTable with
      ⟨rfl, hthroughTableCap⟩
    rcases (checkedAdd_eq_some_iff B
      (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n)
      (idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)
      throughIndex).mp hthroughIndex with
      ⟨rfl, hthroughIndexCap⟩
    rcases (checkedAdd_eq_some_iff B
      (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
        idxWidth (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n)
      ((treeCircuitWitnessCodec (thresholdPoly k)).witnessBits n) total).mp
        htotal with ⟨rfl, htotalCap⟩
    subst s
    constructor
    · constructor <;> rfl
    · exact htotalCap
  · rintro ⟨hexact, hMCap⟩
    have hs := hexact.eq_exactContentSizes
    subst s
    let codec := treeCircuitWitnessCodec (thresholdPoly k)
    change treeMCSPPrefixM codec n ≤ B at hMCap
    have hWLeM : codec.witnessBits n ≤ treeMCSPPrefixM codec n := by
      unfold treeMCSPPrefixM
      omega
    have hTableLeM : Pnp3.Models.Partial.tableLen n ≤
        treeMCSPPrefixM codec n := tableLen_le_treeMCSPPrefixM codec n
    have hGammaLeM : gammaLen n ≤ treeMCSPPrefixM codec n := by
      unfold treeMCSPPrefixM
      omega
    have hIndexLeM : idxWidth codec.witnessBits n ≤
        treeMCSPPrefixM codec n := by
      unfold treeMCSPPrefixM
      omega
    have hThresholdLeW : thresholdPoly k n ≤ codec.witnessBits n := by
      exact threshold_le_concrete_witnessBits k n
    have hThresholdCap : thresholdPoly k n ≤ B :=
      le_trans hThresholdLeW (le_trans hWLeM hMCap)
    have hPowCap : n ^ k ≤ B := by
      unfold thresholdPoly at hThresholdCap
      omega
    have hNBitsCap : bitLength n ≤ B :=
      le_trans (bitLength_le_concrete_witnessBits k n)
        (le_trans hWLeM hMCap)
    have hWitnessFactorCap : bitLength n + 4 ≤ B :=
      le_trans (witnessFactor_le_concrete_witnessBits k n)
        (le_trans hWLeM hMCap)
    have hTableCap : Pnp3.Models.Partial.tableLen n ≤ B :=
      le_trans hTableLeM hMCap
    have hWitnessCap : codec.witnessBits n ≤ B :=
      le_trans hWLeM hMCap
    have hGammaCap : gammaLen n ≤ B :=
      le_trans hGammaLeM hMCap
    have hIndexCap : idxWidth codec.witnessBits n ≤ B :=
      le_trans hIndexLeM hMCap
    have hTagGammaCap : tagLen + gammaLen n ≤ B := by
      unfold treeMCSPPrefixM at hMCap
      omega
    have hThroughTableCap :
        tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n ≤ B := by
      unfold treeMCSPPrefixM at hMCap
      omega
    have hThroughIndexCap :
        tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
          idxWidth codec.witnessBits n ≤ B := by
      unfold treeMCSPPrefixM at hMCap
      omega
    simp only [exactContentSizes]
    refine ⟨n ^ k,
      (checkedPow_eq_some_iff B n k (n ^ k)).mpr ⟨rfl, hPowCap⟩,
      thresholdPoly k n,
      (checkedAdd_eq_some_iff B (n ^ k) k (thresholdPoly k n)).mpr
        ⟨rfl, hThresholdCap⟩,
      bitLength n,
      (checkedBitLength_eq_some_iff B n (bitLength n)).mpr
        ⟨rfl, hNBitsCap⟩,
      bitLength n + 4,
      (checkedAdd_eq_some_iff B (bitLength n) 4 (bitLength n + 4)).mpr
        ⟨rfl, hWitnessFactorCap⟩,
      codec.witnessBits n,
      (checkedMul_eq_some_iff B (bitLength n + 4) (thresholdPoly k n)
        (codec.witnessBits n)).mpr ⟨rfl, hWitnessCap⟩,
      Pnp3.Models.Partial.tableLen n,
      (checkedTableLen_eq_some_iff B n
        (Pnp3.Models.Partial.tableLen n)).mpr ⟨rfl, hTableCap⟩,
      exactGammaSizes n,
      (checkedGammaSizes_eq_some_iff B n (exactGammaSizes n)).mpr
        ⟨rfl, hGammaCap⟩,
      idxWidth codec.witnessBits n,
      (checkedIndexWidth_eq_some_iff B (codec.witnessBits n)
        (idxWidth codec.witnessBits n)).mpr ?_,
      tagLen + gammaLen n,
      (checkedAdd_eq_some_iff B tagLen (gammaLen n)
        (tagLen + gammaLen n)).mpr ⟨rfl, hTagGammaCap⟩,
      tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n,
      (checkedAdd_eq_some_iff B (tagLen + gammaLen n)
        (Pnp3.Models.Partial.tableLen n)
        (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n)).mpr
          ⟨rfl, hThroughTableCap⟩,
      tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
        idxWidth codec.witnessBits n,
      (checkedAdd_eq_some_iff B
        (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n)
        (idxWidth codec.witnessBits n)
        (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
          idxWidth codec.witnessBits n)).mpr ⟨rfl, hThroughIndexCap⟩,
      treeMCSPPrefixM codec n, ?_, ?_⟩
    · change
        idxWidth codec.witnessBits n = bitLength (codec.witnessBits n) ∧
          bitLength (codec.witnessBits n) ≤ B
      exact ⟨rfl, hIndexCap⟩
    · apply (checkedAdd_eq_some_iff B
        (tagLen + gammaLen n + Pnp3.Models.Partial.tableLen n +
          idxWidth codec.witnessBits n)
        (codec.witnessBits n) (treeMCSPPrefixM codec n)).mpr
      exact ⟨rfl, hMCap⟩
    · rfl
/-- Exact overflow characterization at the authoritative repository `M`. -/
theorem computeContentSizesCapped_eq_none_iff (k B n : Nat) :
    computeContentSizesCapped k B n = none ↔
      B < treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k)) n := by
  constructor
  · intro hnone
    by_contra hnot
    have hcap : treeMCSPPrefixM
        (treeCircuitWitnessCodec (thresholdPoly k)) n ≤ B :=
      Nat.le_of_not_gt hnot
    have hsome := (computeContentSizesCapped_eq_some_iff k B n
      (exactContentSizes k n)).mpr
      ⟨exactContentSizes_exact k n, by
        simpa [exactContentSizes] using hcap⟩
    rw [hnone] at hsome
    contradiction
  · intro hover
    cases hrun : computeContentSizesCapped k B n with
    | none => rfl
    | some s =>
        have hspec :=
          (computeContentSizesCapped_eq_some_iff k B n s).mp hrun
        have hM := hspec.1.M_eq
        have : treeMCSPPrefixM
            (treeCircuitWitnessCodec (thresholdPoly k)) n ≤ B := by
          rw [← hM]
          exact hspec.2
        exact False.elim ((Nat.not_le_of_lt hover) this)
/-- Successful computations retain the concrete witness-width component bound. -/
theorem computeContentSizesCapped_witnessBits_le_M
    {k B n : Nat} {s : ContentSizes}
    (h : computeContentSizesCapped k B n = some s) :
    s.witnessBits ≤ s.M :=
  ((computeContentSizesCapped_eq_some_iff k B n s).mp h).1.witnessBits_le_M
/-- Successful computations retain the truth-table component bound. -/
theorem computeContentSizesCapped_tableLen_le_M
    {k B n : Nat} {s : ContentSizes}
    (h : computeContentSizesCapped k B n = some s) :
    s.tableLen ≤ s.M :=
  ((computeContentSizesCapped_eq_some_iff k B n s).mp h).1.tableLen_le_M
/-- Both principal components are also bounded by the caller's cap. -/
theorem computeContentSizesCapped_components_le_cap
    {k B n : Nat} {s : ContentSizes}
    (h : computeContentSizesCapped k B n = some s) :
    s.witnessBits ≤ B ∧ s.tableLen ≤ B := by
  have hs := (computeContentSizesCapped_eq_some_iff k B n s).mp h
  exact ⟨le_trans hs.1.witnessBits_le_M hs.2,
    le_trans hs.1.tableLen_le_M hs.2⟩
/-- Optional proved-result packaging; it contains no provider or advice. -/
structure CappedContentSizesCertificate (k B n : Nat) where
  sizes : ContentSizes
  exactness : sizes.Exact k n
  M_le_cap : sizes.M ≤ B
  witnessBits_le_M : sizes.witnessBits ≤ sizes.M
  tableLen_le_M : sizes.tableLen ≤ sizes.M
/-- Package any successful computation as the proved result record. -/
def CappedContentSizesCertificate.ofSuccess
    {k B n : Nat} {s : ContentSizes}
    (h : computeContentSizesCapped k B n = some s) :
    CappedContentSizesCertificate k B n :=
  let hs := (computeContentSizesCapped_eq_some_iff k B n s).mp h
  {
    sizes := s
    exactness := hs.1
    M_le_cap := hs.2
    witnessBits_le_M := hs.1.witnessBits_le_M
    tableLen_le_M := hs.1.tableLen_le_M
  }
end ContractExpansion
end Frontier
end Pnp4
