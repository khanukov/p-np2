import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionCoincidence
import Pnp4.Frontier.ContractExpansion.ContentPrefixExtensionPadding
import Pnp4.Frontier.ContractExpansion.ConcreteTreeCodec
import Pnp4.Frontier.ContractExpansion.ThresholdGrowth

/-!
# Content-prefix gate closure — I1

This module closes the residual specification-side gates identified in
`VERIFIER_RETARGET_PLAN.md` §4.3.

* `treeMCSPPrefixM` is strictly monotone, hence injective, when the codec's witness width is
  monotone.  The concrete `treeCircuitWitnessCodec (thresholdPoly k)` satisfies that premise.
  There is deliberately no codec-generic injectivity theorem: `TreeCircuitWitnessCodec` places no
  monotonicity constraint on `witnessBits`.  A definition-level codec construction can therefore
  make adjacent convention lengths collide; no formal counterexample-codec theorem is claimed here.
* A successful gamma decode is canonical without an extra hypothesis: its consumed width is
  `gammaLen` of the decoded target.  Narrowing the content-header decode to the convention window
  uses a consumed-based transfer argument; the support-size/fuel premise of
  `decodeGammaAux?_padWord_canonical`, stated in terms of the original word, cannot be discharged
  here, because the target window may be narrower than the original support.
* Consequently the strict parser's convention-length gate is unconditionally vacuous after a
  successful content-header decode.  `contentInput?_isSome_iff_of_header` leaves exactly three
  conjuncts, carrying the tag value, the decoded index bound, and zero inactive padding.  Each of
  the three is stated as a *successful read with a given value*, so read-success for the tag field,
  the index field and the inactive suffix is bundled into them rather than discharged separately;
  what is discharged unconditionally is the length gate and the three range-only slice obligations
  (`x`, the active prefix `p`, and the padding slice).  No fourth open premise remains, and no
  lemma here asserts that those three reads always succeed.

These results concern the parser and `ContentAccepts` specification only.  Padding invariance is
still proved only for complete words, not for the `ContentPrefixExtensionLanguage` wrapper;
non-vacuity of `ContentAccepts` is not proved.  No verifier TM, runtime accounting theorem, or
`TM.accepts = ContentAccepts` bridge is constructed, and the repository machine model's
unrestricted `runTime` advice channel remains unenforced.  Although the accepted-target polynomial
bound is already proved, machine feasibility and `L' ∈ NP` remain open.

**Progress classification (AGENTS.md): Infrastructure.**  This gate/API closure reduces neither
`VerifiedNPDAGLowerBoundSource` nor `SearchMCSPWeakLowerBound`, proves no lower bound, and carries
**no `P ≠ NP` claim**.
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-! ## Monotonicity and the honest injectivity boundary -/

/-- `bitLength` is monotone.  This proof uses the repository's two-sided power bounds rather than
depending on a separate `Nat.log2` monotonicity API. -/
private theorem bitLength_monotone : Monotone bitLength := by
  intro a b hab
  by_cases ha : a = 0
  · simp [bitLength, ha]
  · by_contra hcon
    have hapos : 0 < a := Nat.pos_of_ne_zero ha
    have haUpper : a < 2 ^ bitLength a := nat_lt_two_pow_bitLength a
    have haLower : 2 ^ (bitLength a - 1) ≤ a := two_pow_bitLength_pred_le hapos
    have hbUpper : b < 2 ^ bitLength b := nat_lt_two_pow_bitLength b
    have hpowers : 2 ^ bitLength b ≤ 2 ^ (bitLength a - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega

/-- `tableLen n = 2^n` is strictly monotone. -/
private theorem tableLen_strictMono : StrictMono Pnp3.Models.Partial.tableLen := by
  intro a b hab
  unfold Pnp3.Models.Partial.tableLen
  exact Nat.pow_lt_pow_right (by omega) hab

/-- Under monotone witness width, the convention length is strictly monotone.  The premise is
essential: a generic codec may vary its otherwise unconstrained `witnessBits` non-monotonically. -/
theorem treeMCSPPrefixM_strictMono {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    StrictMono (treeMCSPPrefixM codec) := by
  intro a b hab
  have hgamma : gammaLen a ≤ gammaLen b := by
    unfold gammaLen
    have h := bitLength_monotone (show a + 1 ≤ b + 1 by omega)
    omega
  have hidx : idxWidth codec.witnessBits a ≤ idxWidth codec.witnessBits b :=
    bitLength_monotone (hmono hab.le)
  have hwitness : codec.witnessBits a ≤ codec.witnessBits b := hmono hab.le
  have htable : Pnp3.Models.Partial.tableLen a < Pnp3.Models.Partial.tableLen b :=
    tableLen_strictMono hab
  unfold treeMCSPPrefixM
  omega

/-- The convention length is injective for codecs whose witness width is monotone.  This is the
general valid boundary; no injectivity claim is made for an arbitrary codec. -/
theorem treeMCSPPrefixM_injective_of_monotone {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits) :
    Function.Injective (treeMCSPPrefixM codec) :=
  (treeMCSPPrefixM_strictMono codec hmono).injective

/-- The concrete tree codec at polynomial threshold has monotone witness width. -/
theorem witnessBits_monotone_treePoly (k : Nat) :
    Monotone (treeCircuitWitnessCodec (thresholdPoly k)).witnessBits := by
  show Monotone (fun n => (bitLength n + 4) * thresholdPoly k n)
  intro a b hab
  have hbits : bitLength a ≤ bitLength b := bitLength_monotone hab
  have hthreshold : thresholdPoly k a ≤ thresholdPoly k b := by
    unfold thresholdPoly
    have hpow := Nat.pow_le_pow_left hab k
    omega
  exact Nat.mul_le_mul (by omega) hthreshold

/-- The convention length is injective for the concrete polynomial-threshold tree codec. -/
theorem treeMCSPPrefixM_injective_treePoly (k : Nat) :
    Function.Injective (treeMCSPPrefixM (treeCircuitWitnessCodec (thresholdPoly k))) :=
  treeMCSPPrefixM_injective_of_monotone _ (witnessBits_monotone_treePoly k)

/-- **`hn`-free coincidence.**  Monotonicity of the witness width turns parse inversion's equality
of convention lengths into equality of targets, discharging the old explicit `input.n = n`
premise. -/
theorem ContentPrefixExtendable_iff_of_parse' {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold)
    (hmono : Monotone codec.witnessBits)
    {n : Nat} (y : PrefixBitVec (treeMCSPPrefixM codec n))
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec n))
    (hparse : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ContentPrefixExtendable codec y
      ↔ PrefixExtendable (treeMCSPConcretePrefixParser threshold codec) y := by
  have hlength :=
    (parseTreeMCSPPrefixInput_inversion threshold codec y input hparse).1
  have hn : input.n = n :=
    treeMCSPPrefixM_injective_of_monotone codec hmono hlength.symm
  exact ContentPrefixExtendable_iff_of_parse codec y input hparse hn

/-! ## Gamma canonicity and consumed-based narrowing -/

/-- A successful fixed-width big-endian read is strictly below `2 ^ width`. -/
theorem readNatBE_lt_two_pow {m : Nat} (y : PrefixBitVec m) (offset width : Nat)
    {v : Nat} (h : readNatBE y offset width = some v) :
    v < 2 ^ width := by
  induction width generalizing offset v with
  | zero =>
      simp [readNatBE] at h
      omega
  | succ k ih =>
      rw [readNatBE] at h
      cases hbit : readBit? y offset with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          cases hrest : readNatBE y (offset + 1) k with
          | none => rw [hrest] at h; cases h
          | some rest =>
              rw [hrest] at h
              have hrestBound : rest < 2 ^ k := ih (offset + 1) hrest
              have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by
                rw [Nat.pow_succ]
                omega
              have hv : (if b then (2 : Nat) ^ k else 0) + rest = v := by
                simpa using h
              have hbitBound : (if b then (2 : Nat) ^ k else 0) ≤ 2 ^ k := by
                cases b <;> simp
              omega

/-- A two-sided adjacent-power bound determines `bitLength`. -/
private theorem bitLength_eq_of_pow_bounds {a zeros : Nat}
    (hlo : 2 ^ zeros ≤ a) (hhi : a < 2 ^ (zeros + 1)) :
    bitLength a = zeros + 1 := by
  have hapos : 0 < a := lt_of_lt_of_le (Nat.pow_pos (by omega)) hlo
  have haUpper : a < 2 ^ bitLength a := nat_lt_two_pow_bitLength a
  have haLower : 2 ^ (bitLength a - 1) ≤ a := two_pow_bitLength_pred_le hapos
  have hbitPos : 0 < bitLength a := bitLength_pos_of_pos hapos
  have hupper : bitLength a ≤ zeros + 1 := by
    by_contra hcon
    have hpowers : 2 ^ (zeros + 1) ≤ 2 ^ (bitLength a - 1) :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  have hlower : zeros + 1 ≤ bitLength a := by
    by_contra hcon
    have hpowers : 2 ^ bitLength a ≤ 2 ^ zeros :=
      Nat.pow_le_pow_right (by omega) (by omega)
    omega
  omega

/-- Every successful auxiliary gamma scan has consumed at least the portion contributed by its
current zero count.  This is the range invariant needed by the narrowing transfer. -/
private theorem decodeGammaAux?_consumed_ge {m : Nat} (y : PrefixBitVec m) {offset : Nat} :
    ∀ {fuel zeros n' consumed : Nat},
      decodeGammaAux? y offset fuel zeros = some (n', consumed) →
        2 * zeros + 1 ≤ consumed := by
  intro fuel
  induction fuel with
  | zero => intro zeros n' consumed h; cases h
  | succ remaining ih =>
      intro zeros n' consumed h
      rw [decodeGammaAux?] at h
      cases hbit : readBit? y (offset + zeros) with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          cases b with
          | true =>
              cases hpayload : readNatBE y (offset + zeros + 1) zeros with
              | none => rw [hpayload] at h; cases h
              | some payload =>
                  rw [hpayload] at h
                  simp at h
                  omega
          | false =>
              have hnext := ih (zeros := zeros + 1) (by simpa using h)
              omega

/-- A successful auxiliary gamma scan consumes the canonical gamma width of its decoded value. -/
private theorem decodeGammaAux?_consumed_eq_gammaLen {m : Nat}
    (y : PrefixBitVec m) {offset : Nat} :
    ∀ {fuel zeros n' consumed : Nat},
      decodeGammaAux? y offset fuel zeros = some (n', consumed) →
        consumed = gammaLen n' := by
  intro fuel
  induction fuel with
  | zero => intro zeros n' consumed h; cases h
  | succ remaining ih =>
      intro zeros n' consumed h
      rw [decodeGammaAux?] at h
      cases hbit : readBit? y (offset + zeros) with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          cases b with
          | true =>
              cases hpayload : readNatBE y (offset + zeros + 1) zeros with
              | none => rw [hpayload] at h; cases h
              | some payload =>
                  rw [hpayload] at h
                  simp at h
                  have hpayloadBound : payload < 2 ^ zeros :=
                    readNatBE_lt_two_pow y _ _ hpayload
                  have hpowPos : 0 < 2 ^ zeros := Nat.pow_pos (by omega)
                  have hvalue : n' + 1 = 2 ^ zeros + payload := by omega
                  have hbits : bitLength (n' + 1) = zeros + 1 := by
                    refine bitLength_eq_of_pow_bounds (by omega) ?_
                    have hpow : 2 ^ (zeros + 1) = 2 ^ zeros + 2 ^ zeros := by
                      rw [Nat.pow_succ]
                      omega
                    omega
                  unfold gammaLen
                  omega
          | false =>
              exact ih (by simpa using h)

/-- **Hypothesis-free gamma canonicity.**  Successful decoding alone determines the consumed
width; no canonicality or range premise is required from a caller. -/
theorem decodeGamma?_consumed_eq_gammaLen {m : Nat} (y : PrefixBitVec m)
    {offset n' consumed : Nat}
    (h : decodeGamma? y offset = some (n', consumed)) :
    consumed = gammaLen n' := by
  unfold decodeGamma? at h
  exact decodeGammaAux?_consumed_eq_gammaLen y h

/-- Content-header specialization of hypothesis-free gamma canonicity. -/
theorem contentHeader?_consumed_eq_gammaLen {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat} (hheader : contentHeader? z = some (n', consumed)) :
    consumed = gammaLen n' := by
  unfold contentHeader? at hheader
  exact decodeGamma?_consumed_eq_gammaLen _ hheader

/-- Transfer a successful gamma scan between two paddings using the consumed width, rather than an
invalid fuel bound involving the original support.  Both side conditions are preserved by a blank
scan step. -/
private theorem decodeGammaAux?_padWord_narrow_aux {N : Nat} (z : PrefixBitVec N)
    {offset : Nat} :
    ∀ {T T' fuel fuel' zeros n' consumed : Nat},
      offset + consumed ≤ T' →
      consumed + 1 ≤ 2 * (fuel' + zeros) →
      decodeGammaAux? (padWord z T) offset fuel zeros = some (n', consumed) →
      decodeGammaAux? (padWord z T') offset fuel' zeros = some (n', consumed) := by
  intro T T' fuel
  induction fuel with
  | zero => intro fuel' zeros n' consumed _ _ h; cases h
  | succ remaining ih =>
      intro fuel' zeros n' consumed hwidth hfuel h
      have hconsumed : 2 * zeros + 1 ≤ consumed :=
        decodeGammaAux?_consumed_ge (padWord z T) h
      obtain ⟨nextFuel, rfl⟩ : ∃ nextFuel, fuel' = nextFuel + 1 :=
        ⟨fuel' - 1, by omega⟩
      rw [decodeGammaAux?] at h ⊢
      cases hbit : readBit? (padWord z T) (offset + zeros) with
      | none => rw [hbit] at h; cases h
      | some b =>
          rw [hbit] at h
          have hsourceRange : offset + zeros < T := by
            by_contra hnot
            rw [readBit?_padWord_of_ge z (show T ≤ offset + zeros by omega)] at hbit
            cases hbit
          rw [readBit?_padWord_of_lt z hsourceRange] at hbit
          have htargetBit : readBit? (padWord z T') (offset + zeros) = some b := by
            rw [readBit?_padWord_of_lt z (show offset + zeros < T' by omega)]
            exact hbit
          rw [htargetBit]
          cases b with
          | true =>
              cases hpayload : readNatBE (padWord z T) (offset + zeros + 1) zeros with
              | none => rw [hpayload] at h; cases h
              | some payload =>
                  rw [hpayload] at h
                  have hconsumedEq : consumed = 2 * zeros + 1 := by
                    have h' := h
                    simp at h'
                    omega
                  rw [readNatBE_padWord_transfer z
                    (show offset + zeros + 1 + zeros ≤ T' by omega) hpayload]
                  exact h
          | false =>
              exact ih (by omega) (by omega) h

/-- **Unconditional narrowing.**  A successful content-header decode re-succeeds with exactly the
same target and consumed width on the target's convention window. -/
theorem decodeGamma?_padWord_narrow {N : Nat} (z : PrefixBitVec N)
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen = some (n', consumed) := by
  have hcanonical : consumed = gammaLen n' :=
    contentHeader?_consumed_eq_gammaLen z hheader
  have hwidth : tagLen + consumed ≤ treeMCSPPrefixM codec n' := by
    rw [hcanonical]
    exact gammaLen_le_treeMCSPPrefixM codec n'
  unfold contentHeader? at hheader
  unfold decodeGamma? at hheader ⊢
  exact decodeGammaAux?_padWord_narrow_aux z hwidth (by omega) hheader

/-- **Unconditional length-gate vacuity.**  Any successful narrow re-decode after a successful
content header returns the same target, so the parser's convention-length comparison is reflexive. -/
theorem contentInput?_lengthGate_vacuous {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed n_dec consumed_dec : Nat}
    (hheader : contentHeader? z = some (n', consumed))
    (hnarrow : decodeGamma? (padWord z (treeMCSPPrefixM codec n')) tagLen =
      some (n_dec, consumed_dec)) :
    n_dec = n' ∧ treeMCSPPrefixM codec n' = treeMCSPPrefixM codec n_dec := by
  have hcanonical := decodeGamma?_padWord_narrow z codec hheader
  have hpairs : (n_dec, consumed_dec) = (n', consumed) :=
    Option.some.inj (hnarrow.symm.trans hcanonical)
  have hn : n_dec = n' := congrArg Prod.fst hpairs
  exact ⟨hn, by simp [hn]⟩

/-! ## Exact parser residue -/

/-- A bit slice succeeds whenever its interval fits. -/
private theorem sliceBits?_isSome_of_range {m : Nat} (y : PrefixBitVec m)
    {offset width : Nat} (hfit : offset + width ≤ m) :
    ∃ v, sliceBits? y offset width = some v := by
  exact ⟨_, by rw [sliceBits?, dif_pos hfit]⟩

/-- A successful strict parse exposes exactly the tag, index-bound and pad-zero value tests. -/
private theorem parseTreeMCSPPrefixInput_value_tests
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    readNatBE y 0 tagLen = some treePrefixTag
      ∧ ∃ consumed : Nat, decodeGamma? y tagLen = some (input.n, consumed)
          ∧ readNatBE y (tagLen + consumed + Pnp3.Models.Partial.tableLen input.n)
              (idxWidth codec.witnessBits input.n) = some input.i
          ∧ input.i ≤ codec.witnessBits input.n
          ∧ allZeroSlice? y
              (tagLen + consumed + Pnp3.Models.Partial.tableLen input.n
                + idxWidth codec.witnessBits input.n + input.i)
              (codec.witnessBits input.n - input.i) = some true := by
  unfold parseTreeMCSPPrefixInput at h
  cases htagRead : readNatBE y 0 tagLen with
  | none => simp [htagRead] at h
  | some tag =>
      simp [htagRead] at h
      by_cases htag : tag = treePrefixTag
      · simp [htag] at h
        cases hgamma : decodeGamma? y tagLen with
        | none => simp [hgamma] at h
        | some decoded =>
            obtain ⟨n', consumed⟩ := decoded
            simp [hgamma] at h
            by_cases hlength : m = treeMCSPPrefixM codec n'
            · simp [hlength] at h
              cases hx : sliceBits? y (tagLen + consumed)
                  (Pnp3.Models.Partial.tableLen n') with
              | none => simp [hx] at h
              | some x =>
                  simp [hx] at h
                  cases hiRead : readNatBE y
                      (tagLen + consumed + Pnp3.Models.Partial.tableLen n')
                      (idxWidth codec.witnessBits n') with
                  | none => simp [hiRead] at h
                  | some i =>
                      simp [hiRead] at h
                      by_cases hi : i ≤ codec.witnessBits n'
                      · simp [hi] at h
                        cases hp : sliceBits? y
                            (tagLen + consumed + Pnp3.Models.Partial.tableLen n'
                              + idxWidth codec.witnessBits n') i with
                        | none => simp [hp] at h
                        | some p =>
                            simp [hp] at h
                            cases hpad : sliceBits? y
                                (tagLen + consumed + Pnp3.Models.Partial.tableLen n'
                                  + idxWidth codec.witnessBits n' + i)
                                (codec.witnessBits n' - i) with
                            | none => simp [hpad] at h
                            | some pad =>
                                simp [hpad] at h
                                cases hzero : allZeroSlice? y
                                    (tagLen + consumed + Pnp3.Models.Partial.tableLen n'
                                      + idxWidth codec.witnessBits n' + i)
                                    (codec.witnessBits n' - i) with
                                | none => simp [hzero] at h
                                | some padZero =>
                                    simp [hzero] at h
                                    by_cases hz : padZero = true
                                    · simp [hz] at h
                                      cases h
                                      refine ⟨by simp [htag], consumed, by simp, ?_, hi, ?_⟩
                                      · simpa using hiRead
                                      · simpa [hz] using hzero
                                    · simp [hz] at h
                      · simp [hi] at h
            · simp [hlength] at h
      · simp [htag] at h

/-- Given a successful content-header decode, `contentInput?` succeeds **iff** exactly the three
remaining parser tests pass: the tag read succeeds with value `treePrefixTag`; the index read
succeeds with a value within the witness width; and the inactive-suffix read succeeds with value
`true`.  The range-only slice obligations and the convention-length gate are discharged
unconditionally; the read-success parts of the tag/index/padding checks are deliberately bundled in
the three displayed right-hand conjuncts, so there is no separate fourth open premise. -/
theorem contentInput?_isSome_iff_of_header {threshold : Nat → Nat}
    (codec : TreeCircuitWitnessCodec threshold) {N : Nat} (z : PrefixBitVec N)
    {n' consumed : Nat}
    (hheader : contentHeader? z = some (n', consumed)) :
    (contentInput? codec z).isSome ↔
      readNatBE (padWord z (treeMCSPPrefixM codec n')) 0 tagLen = some treePrefixTag
        ∧ ∃ i : Nat,
          readNatBE (padWord z (treeMCSPPrefixM codec n'))
              (tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n')
              (idxWidth codec.witnessBits n') = some i
            ∧ i ≤ codec.witnessBits n'
            ∧ allZeroSlice? (padWord z (treeMCSPPrefixM codec n'))
                (tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n'
                  + idxWidth codec.witnessBits n' + i)
                (codec.witnessBits n' - i) = some true := by
  let y := padWord z (treeMCSPPrefixM codec n')
  have hgamma : decodeGamma? y tagLen = some (n', gammaLen n') := by
    rw [show gammaLen n' = consumed from (contentHeader?_consumed_eq_gammaLen z hheader).symm]
    exact decodeGamma?_padWord_narrow z codec hheader
  constructor
  · intro hsome
    unfold contentInput? at hsome
    simp only [hheader] at hsome
    have hparseSome : (parseTreeMCSPPrefixInput threshold codec y).isSome := by
      simpa [y] using hsome
    cases hparse : parseTreeMCSPPrefixInput threshold codec y with
    | none => simp [hparse] at hparseSome
    | some input =>
        have htests := parseTreeMCSPPrefixInput_value_tests codec y input hparse
        obtain ⟨htag, cg, hgammaInput, hiRead, hi, hzero⟩ := htests
        have hpairs : (input.n, cg) = (n', gammaLen n') :=
          Option.some.inj (hgammaInput.symm.trans hgamma)
        have hnInput : input.n = n' := congrArg Prod.fst hpairs
        have hcg : cg = gammaLen n' := congrArg Prod.snd hpairs
        rw [hnInput] at hiRead hi hzero
        rw [hcg] at hiRead hzero
        exact ⟨htag, input.i, hiRead, hi, hzero⟩
  · rintro ⟨htag, i, hiRead, hi, hzero⟩
    change readNatBE y 0 tagLen = some treePrefixTag at htag
    change readNatBE y
      (tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n')
      (idxWidth codec.witnessBits n') = some i at hiRead
    change allZeroSlice? y
      (tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n'
        + idxWidth codec.witnessBits n' + i)
      (codec.witnessBits n' - i) = some true at hzero
    have hlayout : tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n'
        + idxWidth codec.witnessBits n' + codec.witnessBits n' =
        treeMCSPPrefixM codec n' := by
      unfold treeMCSPPrefixM
      omega
    obtain ⟨x, hx⟩ := sliceBits?_isSome_of_range y
      (offset := tagLen + gammaLen n')
      (width := Pnp3.Models.Partial.tableLen n') (by omega)
    obtain ⟨p, hp⟩ := sliceBits?_isSome_of_range y
      (offset := tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n'
        + idxWidth codec.witnessBits n') (width := i) (by omega)
    obtain ⟨pad, hpad⟩ := sliceBits?_isSome_of_range y
      (offset := tagLen + gammaLen n' + Pnp3.Models.Partial.tableLen n'
        + idxWidth codec.witnessBits n' + i)
      (width := codec.witnessBits n' - i) (by omega)
    have hparseSome : (parseTreeMCSPPrefixInput threshold codec y).isSome := by
      simp [parseTreeMCSPPrefixInput, htag, hgamma, hx, hiRead, hi, hp, hpad, hzero]
    unfold contentInput?
    simp only [hheader]
    simpa [y] using hparseSome

end ContractExpansion
end Frontier
end Pnp4
