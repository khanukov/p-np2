import Pnp4.Frontier.ContractExpansion.ContentPrefixExtension

/-!
# Truth-table field recovery from a successful parse — FEAS-0 slice, part 1

`VERIFIER_RETARGET_PLAN.md` §1.0 (the FEAS-0 feasibility gate) needs to turn a semantic fact about
the *parsed* truth table `pr.2.x` into a fact about cells of the *ambient* word `z`.  The existing
parse inversion `parseTreeMCSPPrefixInput_inversion`
(`ContentPrefixExtensionCoincidence.lean:140`) exposes only the length gate and the gamma decode; it
discards the `x` branch of the success cascade.  This module re-walks that same cascade and keeps the
`x` branch instead:

* `parseTreeMCSPPrefixInput_x_slice` — a successful strict parse pins `input.x` to the canonical
  `x`-slice of its own ambient vector, at offset `tagLen + consumed` for the gamma width `consumed`
  the parse actually consumed;
* `contentInput?_x_apply` — the content-side pointwise form: the parsed truth table is a
  blank-padded read of `z` itself, at offsets `tagLen + cg + j`.

Both are dependency-closed on `main`: nothing below `ContentPrefixExtension.lean` /
`PrefixParserConvention.lean` is used, and no other declaration in this module is public.

**`consumed` is carried symbolically — this slice is I1-free (plan §1.0 stop/go F0b).**  Neither
statement says `consumed = gammaLen input.n`, and neither uses injectivity of `treeMCSPPrefixM codec`
(`treeMCSPPrefixM_injective_treePoly` / `_of_monotone`) or gamma canonicity
(`decodeGamma?_consumed_eq_gammaLen`).  Those three are I1 outputs and now exist, in
`ContentPrefixExtensionGateClosure.lean`; this module neither imports that module nor cites any of
them, so the F0b constraint holds at import level and not merely because the names were once
missing.  The single symbolic `consumed` produced by the cascade is
what couples the header decode and the field slice: both conjuncts of
`parseTreeMCSPPrefixInput_x_slice` are stated under the *same* existential witness, which is exactly
what the consumer needs and all that the parser guarantees.  No range side condition appears either
— a successful parse has already produced the slice, so its fit is a consequence, not a premise.

**Scope — what this does not buy.**  These are field-recovery facts about the strict parser, nothing
more.  In particular they do **not** bound the decoded target (the now-landed FEAS-0 headline lives
in slice part 2, `ContentTargetSizeBound.lean`), they do **not themselves** show `ContentAccepts` is
satisfiable, they build no verifier TM, runtime bound or `TM.accepts` bridge for `L'`, and they say
nothing about the strict parser's surviving value tests
(`tag = treePrefixTag`, `i ≤ codec.witnessBits n`, `padZero = true`).  Statements are generic in the
codec because *recovery* is; every FEAS-0 statement that constrains a decode is specialized to
`treeCircuitWitnessCodec (thresholdPoly k)`, where alone it holds (§1.0).
Concrete non-vacuity is supplied separately by GATE-0, and I1 separately proves the
convention-length equality gate vacuous while leaving exactly those three read-value tests.

**Progress classification (AGENTS.md): Infrastructure** — parser field recovery for the NP-verifier
track; proves no separation and reduces neither `VerifiedNPDAGLowerBoundSource` nor
`SearchMCSPWeakLowerBound`.  **No `P ≠ NP` claim.**
-/

namespace Pnp4
namespace Frontier
namespace ContractExpansion

open AlgorithmsToLowerBounds

/-- **Truth-table slice recovery.**  The parser's success cascade pins `input.x` to the canonical
`x`-slice of the ambient word.  `consumed` is the *narrow-window* gamma width, carried
**symbolically**: FEAS-0 never needs `consumed = gammaLen input.n`, so this does not depend on I1,
and no range side condition is needed because a successful parse already produced the slice. -/
theorem parseTreeMCSPPrefixInput_x_slice
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {m : Nat}
    (y : PrefixBitVec m)
    (input : PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec)) m)
    (h : parseTreeMCSPPrefixInput threshold codec y = some input) :
    ∃ consumed : Nat,
      decodeGamma? y tagLen = some (input.n, consumed)
        ∧ sliceBits? y (tagLen + consumed)
            (Pnp3.Models.Partial.tableLen input.n) = some input.x := by
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
            by_cases hlen : m = treeMCSPPrefixM codec n'
            · simp [hlen] at h
              cases hx : sliceBits? y (tagLen + consumed) (Pnp3.Models.Partial.tableLen n') with
              | none => simp [hx] at h
              | some x =>
                  simp [hx] at h
                  cases hiRead : readNatBE y (tagLen + consumed + Pnp3.Models.Partial.tableLen n')
                      (idxWidth codec.witnessBits n') with
                  | none => simp [hiRead] at h
                  | some i =>
                      simp [hiRead] at h
                      by_cases hi : i ≤ codec.witnessBits n'
                      · simp [hi] at h
                        cases hp : sliceBits? y
                            (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                              idxWidth codec.witnessBits n') i with
                        | none => simp [hp] at h
                        | some p =>
                            simp [hp] at h
                            cases hpad : sliceBits? y
                                (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                                  idxWidth codec.witnessBits n' + i)
                                (codec.witnessBits n' - i) with
                            | none => simp [hpad] at h
                            | some pad =>
                                simp [hpad] at h
                                cases hzero : allZeroSlice? y
                                    (tagLen + consumed + Pnp3.Models.Partial.tableLen n' +
                                      idxWidth codec.witnessBits n' + i)
                                    (codec.witnessBits n' - i) with
                                | none => simp [hzero] at h
                                | some padZero =>
                                    simp [hzero] at h
                                    by_cases hz : padZero = true
                                    · simp [hz] at h
                                      cases h
                                      exact ⟨consumed, by simp, by simpa using hx⟩
                                    · simp [hz] at h
                      · simp [hi] at h
            · simp [hlen] at h
      · simp [htag] at h

/-- Content-side pointwise form: the parsed truth table is a blank-padded read of `z` itself.  The
offset shift `cg` is the same symbolic gamma width as above — nothing here identifies it with
`gammaLen pr.2.n`, and nothing relates `pr.2.n` to the header value `pr.1`. -/
theorem contentInput?_x_apply
    {threshold : Nat → Nat} (codec : TreeCircuitWitnessCodec threshold) {N : Nat}
    (z : PrefixBitVec N)
    {pr : Σ r : Nat, PrefixInput
      (treeMCSPSearchProblem threshold (TreeMCSPSearchWitnessEncoding.ofCodec codec))
      (treeMCSPPrefixM codec r)}
    (hpr : contentInput? codec z = some pr) :
    ∃ cg : Nat, ∀ j : Fin (Pnp3.Models.Partial.tableLen pr.2.n),
      pr.2.x j = padRead z (tagLen + cg + j.1) := by
  unfold contentInput? at hpr
  cases hheader : contentHeader? z with
  | none => simp [hheader] at hpr
  | some header =>
      obtain ⟨n', _consumedWide⟩ := header
      simp only [hheader] at hpr
      cases hparse : parseTreeMCSPPrefixInput threshold codec (padWord z (treeMCSPPrefixM codec n'))
        with
      | none => simp [hparse] at hpr
      | some input =>
          simp only [hparse, Option.map_some] at hpr
          cases hpr
          obtain ⟨cg, _, hslice⟩ :=
            parseTreeMCSPPrefixInput_x_slice codec (padWord z (treeMCSPPrefixM codec n')) input
              hparse
          refine ⟨cg, fun j => ?_⟩
          unfold sliceBits? at hslice
          split at hslice
          · exact (congrFun (Option.some.inj hslice) j).symm
          · cases hslice

end ContractExpansion
end Frontier
end Pnp4
