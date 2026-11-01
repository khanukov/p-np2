import Pnp4.Frontier.ContractExpansion.ContentFixedGammaPayloadDispatcherSemanticBridge

/-!
# Header-value meaning of the fixed dispatcher endpoints

This infrastructure bridge turns the G2n endpoint/scan equivalences into exact
statements about the decoded content header.

* The strict payload read is `some 0` exactly when the strict all-zero scan of
  the same window is `some true`, and the scan is `some false` exactly when the
  read succeeds with a positive value.  Neither statement has a fit
  hypothesis: width zero and out-of-range windows are included.
* `contentHeader? z = some (n, consumed)` holds exactly when, for some `zeros`
  and `payload`, the physical terminator scan `gammaZeros?` returns `zeros`,
  the payload read over `[9 + zeros, 9 + 2 * zeros)` at logical length
  `2 * N + 1` returns `payload`, `n + 1 = 2 ^ zeros + payload`, and
  `consumed = 2 * zeros + 1`.  Payload cells at or beyond `N` read as virtual
  zeros; there is no tag, physical-fit, codec, or positivity premise.
* A successful `contentInput?`, for any codec, recovers that header target both
  as its outer Sigma index and as the parsed `PrefixInput` target read by
  `ContentAccepts`.  This direction is one-way.
* On matching tags at the common dispatcher deadline, `qReject` is exactly
  header absence, `qAllZero` is exactly a header `(n, 2 * zeros + 1)` with
  `n + 1 = 2 ^ zeros`, and `qHasOne` is exactly such a header with
  `2 ^ zeros < n + 1`.

The gamma width `zeros` and the payload natural are never identified with the
header target `n`; the parsed target `pr.2.n` equals the header target only
through a successful `contentInput?`.  Nothing here claims that the dispatcher
stores or materializes `n` or the payload on its tape, that any machine
executes `contentInput?` or the parser, that an endpoint is acceptance of the
content language, or anything about untagged input, a uniform head,
cross-machine clock composition, `ContentVerifierBridge`, advice freedom, NP
membership, or lower bounds; this is not P-vs-NP mainline progress.
-/

namespace Pnp4.Frontier.ContractExpansion

open AlgorithmsToLowerBounds
open Pnp3.Complexity.Uniform.V1

namespace VirtualZeroTailReader

/-- The strict all-zero scan is the strict big-endian read tested for zero;
in particular both fail on exactly the same windows. -/
private theorem allZeroSlice?_eq_map_readNatBE
    {N T offset width : Nat} (z : PrefixBitVec N) :
    allZeroSlice? z T offset width =
      (readNatBE z T offset width).map (fun payload => decide (payload = 0)) := by
  induction width generalizing offset with
  | zero => rfl
  | succ k ih =>
      rw [allZeroSlice?, readNatBE, ih]
      cases readBit? z T offset with
      | none => rfl
      | some b =>
          cases readNatBE z T (offset + 1) k with
          | none => rfl
          | some rest => cases b <;> simp

/-- A strict payload read is zero exactly when the strict all-zero scan of the
same window is true.  There is no fit hypothesis: width zero gives `some 0`
and `some true`, and a positive-width window that does not fit makes both
sides false. -/
theorem readNatBE_eq_some_zero_iff_allZeroSlice?_eq_some_true
    {N T offset width : Nat} (z : PrefixBitVec N) :
    readNatBE z T offset width = some 0 ↔
      allZeroSlice? z T offset width = some true := by
  rw [allZeroSlice?_eq_map_readNatBE]
  cases readNatBE z T offset width with
  | none => simp
  | some payload => simp

/-- The strict all-zero scan finds a one exactly when the strict payload read
of the same window succeeds with a positive value.  There is no fit
hypothesis; width zero and non-fitting windows make both sides false. -/
theorem allZeroSlice?_eq_some_false_iff_readNatBE_pos
    {N T offset width : Nat} (z : PrefixBitVec N) :
    allZeroSlice? z T offset width = some false ↔
      ∃ payload, readNatBE z T offset width = some payload ∧ 0 < payload := by
  rw [allZeroSlice?_eq_map_readNatBE]
  cases readNatBE z T offset width with
  | none => simp
  | some payload => simp [Nat.pos_iff_ne_zero]

/-- A strict payload read succeeds whenever its logical window fits. -/
private theorem readNatBE_exists_of_fit
    {N T offset width : Nat} (z : PrefixBitVec N) (hfit : offset + width ≤ T) :
    ∃ payload, readNatBE z T offset width = some payload := by
  induction width generalizing offset with
  | zero => exact ⟨0, rfl⟩
  | succ k ih =>
      obtain ⟨rest, hrest⟩ := ih (offset := offset + 1) (by omega)
      have hoffset : offset < T := by omega
      refine ⟨(if padRead z offset then 2 ^ k else 0) + rest, ?_⟩
      rw [readNatBE, show readBit? z T offset = some (padRead z offset) by
        simp [readBit?, hoffset], hrest]
      rfl

end VirtualZeroTailReader

/-- Decoding along a zero run whose terminator lies inside the logical window
returns the gamma value built from the given payload read. -/
private theorem decodeGammaAux?_zero_run {N T zeros payload : Nat}
    (z : PrefixBitVec N)
    (hterm : tagLen + zeros < T)
    (htrue : padRead z (tagLen + zeros) = true)
    (hfalse : ∀ i, i < zeros → padRead z (tagLen + i) = false)
    (hpayload : VirtualZeroTailReader.readNatBE z T (tagLen + zeros + 1) zeros =
      some payload) :
    ∀ remaining k fuel, k + remaining = zeros → remaining < fuel →
      VirtualZeroTailReader.decodeGammaAux? z T tagLen fuel k =
        some (2 ^ zeros + payload - 1, 2 * zeros + 1) := by
  intro remaining
  induction remaining with
  | zero =>
      intro k fuel hk hfuel
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      have hkz : k = zeros := by omega
      subst hkz
      rw [VirtualZeroTailReader.decodeGammaAux?,
        show VirtualZeroTailReader.readBit? z T (tagLen + k) = some true by
          simp [VirtualZeroTailReader.readBit?, hterm, htrue], hpayload]
      rfl
  | succ remaining ih =>
      intro k fuel hk hfuel
      obtain ⟨fuel, rfl⟩ : ∃ f, fuel = f + 1 := ⟨fuel - 1, by omega⟩
      rw [VirtualZeroTailReader.decodeGammaAux?,
        show VirtualZeroTailReader.readBit? z T (tagLen + k) = some false by
          simp [VirtualZeroTailReader.readBit?, show tagLen + k < T by omega,
            hfalse k (by omega)]]
      simpa using ih (k + 1) fuel (by omega) (by omega)

/-- A decoded gamma width and a payload read at the shared logical length
determine the content header, with the decoder's own subtraction. -/
private theorem contentHeader?_of_gammaZeros_payload {N zeros payload : Nat}
    (z : PrefixBitVec N)
    (hg : FixedContentGammaTerminator.gammaZeros? z = some zeros)
    (hpayload : VirtualZeroTailReader.readNatBE z (2 * N + 1)
      (9 + zeros) zeros = some payload) :
    contentHeader? z = some (2 ^ zeros + payload - 1, 2 * zeros + 1) := by
  obtain ⟨hlt, hterm, hzero⟩ :=
    (FixedContentGammaTerminator.gamma_contract z).1 zeros hg
  have hoffset : tagLen + zeros + 1 = 9 + zeros := by
    unfold tagLen
    omega
  rw [← VirtualZeroTailReader.contentHeader?_eq]
  unfold VirtualZeroTailReader.contentHeader? VirtualZeroTailReader.decodeGamma?
  refine decodeGammaAux?_zero_run z ?_ ?_ ?_ ?_ zeros 0 _ (by omega) ?_
  · unfold tagLen
    omega
  · exact (physicalSymbol_true_iff_padRead_true z).1 hterm
  · intro i hi
    have hsym := hzero i hi
    have hiN : 8 + i < N := by
      unfold FixedContentTagGate.physicalSymbol at hsym
      split at hsym
      · assumption
      · contradiction
    have hread : padRead z (8 + i) = false := by
      simpa [FixedContentTagGate.physicalSymbol, padRead, hiN] using hsym
    exact hread
  · rw [hoffset]
    exact hpayload
  · unfold VirtualZeroTailReader.gammaLoopBound
    omega

/-- Exact, subtraction-free value characterization of the content header: it
decodes to `(n, consumed)` exactly when, for some `zeros` and `payload`, the
physical terminator scan `gammaZeros?` returns `zeros`, the payload read over
`[9 + zeros, 9 + 2 * zeros)` at logical length `2 * N + 1` returns `payload`,
`n + 1 = 2 ^ zeros + payload`, and `consumed = 2 * zeros + 1`.  Payload cells
at or beyond `N` read as virtual zeros.  There is no tag, physical-fit, codec,
or positivity premise. -/
theorem contentHeader?_eq_some_iff_gammaZeros_payload
    {N n consumed : Nat} (z : PrefixBitVec N) :
    contentHeader? z = some (n, consumed) ↔
      ∃ zeros payload,
        FixedContentGammaTerminator.gammaZeros? z = some zeros ∧
        VirtualZeroTailReader.readNatBE z (2 * N + 1)
          (9 + zeros) zeros = some payload ∧
        n + 1 = 2 ^ zeros + payload ∧
        consumed = 2 * zeros + 1 := by
  constructor
  · intro hheader
    obtain ⟨zeros, hg⟩ :
        ∃ zeros, FixedContentGammaTerminator.gammaZeros? z = some zeros :=
      Option.isSome_iff_exists.1
        ((fixedGamma_header_contract z).2 (by simp [hheader]))
    obtain ⟨payload, hpayload⟩ :=
      VirtualZeroTailReader.readNatBE_exists_of_fit z
        (gamma_payload_shared_window_fit z hg)
    have hpair := Option.some.inj
      (hheader.symm.trans (contentHeader?_of_gammaZeros_payload z hg hpayload))
    have hn : n = 2 ^ zeros + payload - 1 := congrArg Prod.fst hpair
    have hconsumed : consumed = 2 * zeros + 1 := congrArg Prod.snd hpair
    have hpow : 0 < 2 ^ zeros := Nat.two_pow_pos zeros
    exact ⟨zeros, payload, hg, hpayload, by omega, hconsumed⟩
  · rintro ⟨zeros, payload, hg, hpayload, hn, hconsumed⟩
    have hpow : 0 < 2 ^ zeros := Nat.two_pow_pos zeros
    rw [contentHeader?_of_gammaZeros_payload z hg hpayload, hconsumed,
      show 2 ^ zeros + payload - 1 = n by omega]

/-- A successful content parse recovers the content-header target twice: as
its outer Sigma index and as the parsed `PrefixInput` target that
`ContentAccepts` reads.  This holds for every codec, with no monotonicity or
injectivity premise. -/
theorem contentInput?_target_eq_contentHeader
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold)
    {N : Nat} (z : PrefixBitVec N)
    {pr : Σ r : Nat,
      PrefixInput
        (treeMCSPSearchProblem threshold
          (TreeMCSPSearchWitnessEncoding.ofCodec codec))
        (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec z = some pr) :
    ∃ consumed,
      contentHeader? z = some (pr.1, consumed) ∧
      pr.2.n = pr.1 := by
  cases hheader : contentHeader? z with
  | none =>
      simp [contentInput?, hheader] at hpr
  | some header =>
      obtain ⟨n', consumed⟩ := header
      cases hparse : parseTreeMCSPPrefixInput threshold codec
          (padWord z (treeMCSPPrefixM codec n')) with
      | none =>
          simp [contentInput?, hheader, hparse] at hpr
      | some input =>
          simp only [contentInput?, hheader, hparse, Option.map_some,
            Option.some.injEq] at hpr
          subst hpr
          obtain ⟨_, consumedDecoded, hdecoded⟩ :=
            parseTreeMCSPPrefixInput_inversion threshold codec _ input hparse
          exact ⟨consumed, rfl,
            (contentInput?_lengthGate_vacuous codec z hheader hdecoded).1⟩

/-- On matching tags, the malformed dispatcher endpoint at the common deadline
is exactly content-header absence. -/
theorem dispatcher_qReject_iff_contentHeader_none
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qReject ↔
      contentHeader? (Fin.append x w) = none := by
  dsimp only
  rw [FixedGammaPayloadDispatcherDeadline.qReject_iff (B := B) x w htag,
    ← Option.not_isSome_iff_eq_none, ← Option.not_isSome_iff_eq_none,
    fixedGamma_header_contract]

/-- On matching tags, `qAllZero` at the common deadline is exactly a decoded
header `(n, 2 * zeros + 1)` whose target satisfies `n + 1 = 2 ^ zeros`, i.e.
a zero payload; width zero gives the header `(0, 1)`. -/
theorem dispatcher_qAllZero_iff_contentHeader_succ_eq_two_pow
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let z := Fin.append x w
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qAllZero ↔
      ∃ n zeros,
        contentHeader? z = some (n, 2 * zeros + 1) ∧
        n + 1 = 2 ^ zeros := by
  have hscan := dispatcher_qAllZero_iff_allZeroSlice_shared_window (B := B) x w htag
  dsimp only at hscan ⊢
  refine hscan.trans ?_
  constructor
  · rintro ⟨zeros, hg, hzero⟩
    have hpayload :=
      (VirtualZeroTailReader.readNatBE_eq_some_zero_iff_allZeroSlice?_eq_some_true
        _).2 hzero
    have hpow : 0 < 2 ^ zeros := Nat.two_pow_pos zeros
    exact ⟨2 ^ zeros - 1, zeros,
      (contentHeader?_eq_some_iff_gammaZeros_payload _).2
        ⟨zeros, 0, hg, hpayload, by omega, rfl⟩, by omega⟩
  · rintro ⟨n, headerZeros, hheader, hn⟩
    obtain ⟨zeros, payload, hg, hpayload, hvalue, hconsumed⟩ :=
      (contentHeader?_eq_some_iff_gammaZeros_payload _).1 hheader
    have hzeros : headerZeros = zeros := by omega
    subst hzeros
    have hzeroPayload : payload = 0 := by omega
    subst hzeroPayload
    exact ⟨headerZeros, hg,
      (VirtualZeroTailReader.readNatBE_eq_some_zero_iff_allZeroSlice?_eq_some_true
        _).1 hpayload⟩

/-- On matching tags, `qHasOne` at the common deadline is exactly a decoded
header `(n, 2 * zeros + 1)` whose target satisfies `2 ^ zeros < n + 1`, i.e.
a positive payload. -/
theorem dispatcher_qHasOne_iff_contentHeader_two_pow_lt_succ
    {a m B : Nat} (x : Bitstring a) (w : Bitstring m)
    (htag : FixedContentTagGate.tagMatches (Fin.append x w) = true) :
    let z := Fin.append x w
    let d := FixedGammaPayloadDispatcher.machine.run
      (FixedGammaPayloadDispatcherDeadline.deadline (a + m))
      (FixedGammaPayloadDispatcher.startConfig B x w)
    d.state = FixedGammaPayloadDispatcher.qHasOne ↔
      ∃ n zeros,
        contentHeader? z = some (n, 2 * zeros + 1) ∧
        2 ^ zeros < n + 1 := by
  have hscan := dispatcher_qHasOne_iff_allZeroSlice_shared_window (B := B) x w htag
  dsimp only at hscan ⊢
  refine hscan.trans ?_
  constructor
  · rintro ⟨zeros, hg, hone⟩
    obtain ⟨payload, hpayload, hpositive⟩ :=
      (VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff_readNatBE_pos _).1 hone
    have hpow : 0 < 2 ^ zeros := Nat.two_pow_pos zeros
    exact ⟨2 ^ zeros + payload - 1, zeros,
      (contentHeader?_eq_some_iff_gammaZeros_payload _).2
        ⟨zeros, payload, hg, hpayload, by omega, rfl⟩, by omega⟩
  · rintro ⟨n, headerZeros, hheader, hlt⟩
    obtain ⟨zeros, payload, hg, hpayload, hvalue, hconsumed⟩ :=
      (contentHeader?_eq_some_iff_gammaZeros_payload _).1 hheader
    have hzeros : headerZeros = zeros := by omega
    subst hzeros
    exact ⟨headerZeros, hg,
      (VirtualZeroTailReader.allZeroSlice?_eq_some_false_iff_readNatBE_pos _).2
        ⟨payload, hpayload, by omega⟩⟩

end Pnp4.Frontier.ContractExpansion
