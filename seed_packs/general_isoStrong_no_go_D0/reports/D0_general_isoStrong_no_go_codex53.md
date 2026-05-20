# Task: general iso-strong no-go D0

Handle: codex53  
Branch: main  
Commit before: a043c690bfec5566be157365963bceda1d375390  
Commit after: (this commit)
Changed files: seed_packs/general_isoStrong_no_go_D0/README.md, seed_packs/general_isoStrong_no_go_D0/WORKER_PROMPT_D0.md, seed_packs/general_isoStrong_no_go_D0/reports/D0_general_isoStrong_no_go_codex53.md, seed_packs/general_isoStrong_no_go_D0/reports/.gitkeep, seed_packs/general_isoStrong_no_go_D0/failures/.gitkeep

## 1. Executive verdict

**INCONCLUSIVE**

Rationale: the canonical contradiction proof is structurally robust and appears to generalize in several core steps, but key generalization lemmas (notably enumeration/cardinality and trace-count control for circuits of size `≤ sYES`) are not yet present as proved interfaces in the inspected files, so a markdown-only argument cannot close a theorem-level refutation of all `IsoStrongFamilyEventually` families.

## 2. Candidate general theorem shape

Strong candidate (most useful if supporting count/enumeration lemmas are added):

```lean
theorem isoStrong_conclusion_negative_general
    (F : GapSliceFamilyEventually)
    (hInDag : ∀ n β, InPpolyDAG (gapPartialMCSP_Language (F.paramsOf n β)))
    (hTof : ∀ n β, F.Tof n β = (F.paramsOf n β).sNO - 1)
    (hMofCount : ∀ n β, F.Mof n (F.Tof n β) = circuitCountBound n (F.Tof n β))
    (hTraceBound : ∀ n β, traceFamilyCard n ((F.paramsOf n β).sYES)
                  ≤ F.Mof n (F.Tof n β)) :
    ¬ IsoStrongFamilyEventually F hInDag
```

Plausible weaker shape: same conclusion but with an explicit abstract finite family `Cand n β` and assumptions that (i) every YES witness trace is realized by some `c ∈ Cand n β` and (ii) `Fintype.card (Cand n β) ≤ F.Mof n (F.Tof n β)`.

## 3. Canonical proof dependency audit

- `F.Mof n (F.Tof n β) = n + 2`  
  **Does not directly generalize**. In canonical track this identity is specific to `sNO=2` and the recurrence base case giving `circuitCountBound n 1 = n+2`. General route needs a replacement equality/inequality tied to `sNO`.

- `sYES = 1`  
  **Canonical-only simplifier**. Needed for the concrete `Size1Candidate` type and exact cardinal `n+2`. General route should replace this by bounded-size witnesses (`≤ sYES`) rather than literal size-1.

- `Size1Candidate` trace count  
  **Generalizes in spirit, not as-is**. The finite-type trick works because candidate family is explicit and tiny. For general `sYES`, finite enumerability is plausible but not currently packaged in inspected interfaces.

- trace-diagonalisation lemma  
  **Likely generalizable** if candidate traces are finite and cardinally bounded below the subcube size. The combinatorial core is generic pigeonhole.

- `exists_valid_agreeing_not_yes_under_slack`  
  **Partially generalizable**. The table-construction/validity/agreement skeleton is generic, but its “not YES” clause currently uses size-1-specific consistency lemmas.

- `slack_for_D_of_isoStrong_slack`  
  **Likely generalizable**. This is mostly arithmetic/extraction from iso-strong slack and should not fundamentally rely on `sYES=1`.

- `CorrectOnPromiseSlice` extraction  
  **Generalizable**. Route-level extraction from `InPpolyDAG` to correctness-on-promise is structural and not tied to canonical constants.

## 4. Replace size-1 traces with size-≤sYES traces

- Finite enumerable family of circuits of size `≤ s`:  
  **Mathematically yes, repository status unclear**. Since syntax trees are finite objects with bounded size over finite constructors/inputs, enumeration should exist.

- Does `circuitCountBound n s` upper-bound traces of such circuits?  
  **Not yet established in inspected interfaces**. In `Model_PartialMCSP.lean`, `circuitCountBound` is documented as an over-approximate recurrence, but this is not by itself a formal theorem that trace-family cardinality is bounded by it.

- Is that enough for diagonalization?  
  **Yes, if formalized**: if number of candidate YES traces on a row-set `D` is `< 2^|D|`, one can choose a label outside their image and derive a diagonal contradiction.

- Existing enumeration/cardinality lemmas already present?  
  **Not visible in required-read files**. Canonical probe file demonstrates size-1 enumeration directly; no generic size-`≤ s` trace-count API is exposed in the inspected interfaces/theorems files.

## 5. Mof relationship

Findings from required-read interface/theorem context:

- Whether general family has
  `F.Mof n (F.Tof n β) = circuitCountBound n (F.Tof n β)`  
  **Plausible for the canonical constructor path; not guaranteed for arbitrary `F` without hypotheses.**

- Whether
  `F.Tof n β = (F.paramsOf n β).sNO - 1`  
  **Appears constructor-level plausible, but must be assumed/proved per family.**

- Whether
  `circuitCountBound p.n p.sYES ≤ F.Mof n (F.Tof n β)`
  follows from `p.gap_ok : p.sYES + 1 ≤ p.sNO`  
  **Not derivable from gap alone in current form.** Gap relates thresholds (`sYES`, `sNO`) but not monotonicity of `circuitCountBound` in the size parameter nor connection to `Mof` unless one adds monotonicity + `Tof = sNO-1` + `Mof = circuitCountBound(...,Tof)` hypotheses.

## 6. General diagonalisation sketch

Conditional sketch (assuming generalized counting infrastructure):

1. From `IsoStrongFamilyEventually`, extract eventual slack:
   `F.Mof n (F.Tof n β) < 2^(tableLen - κ n β)` on admissible slices.
2. Choose `D` with cardinal `tableLen - κ n β` (as in canonical extraction pattern).
3. Define candidate trace set on `D`: evaluations of all YES-eligible circuits (`size ≤ sYES`) restricted to `D`.
4. Use counting lemma to show `|Traces_D| ≤ F.Mof n (F.Tof n β)`.
5. By slack, `|Traces_D| < 2^|D|`; pick label `ℓ : D → Bool` outside trace image.
6. Build diagonal `z` that agrees with YES-side data on required rows and encodes `ℓ` on `D`.
7. Prove `z` is valid and agrees on `D`.
8. If `z ∈ YES`, induced YES witness yields a trace in `Traces_D`, contradicting choice of `ℓ`.
9. Hence `z ∉ YES`, contradict forcing clause of iso-strong.

## 7. Blockers

- Missing generic circuit enumeration API for size `≤ sYES` in required-read surfaces.
- `circuitCountBound` currently appears as recurrence over-approximation, not yet tied (in exposed theorem interfaces) to a proved cardinal bound over YES-witness traces.
- Size-1-specific trace/consistency bridge from canonical proof not yet lifted to arbitrary size threshold.
- Need monotonicity/transport lemmas connecting `gap_ok` and `Tof/Mof` quantitatively.
- Potential “general YES too broad” blocker unless trace abstraction is aligned with exact `PartialMCSP_YES` semantics for bounded-size circuits.

## 8. Recommended next action

**open_circuit_count_trace_bound_L0**

Reason: the highest-leverage blocker is formalizing the missing bound
“number of YES-candidate traces on any finite row-set `D` is ≤ `circuitCountBound n sYES` (or another explicit bound)”, plus transport into `Mof/Tof`. Once this is landed, the existing canonical diagonal skeleton is likely reusable.

---

Outcome:
  REPORT_LANDED

Executive verdict:
  INCONCLUSIVE

General theorem plausible:
  unclear

Key blocker:
  Missing general trace-count/cardinality bridge from bounded-size circuits to `Mof`.

Recommended next action:
  open_circuit_count_trace_bound_L0

Commands run:
  - ./scripts/check.sh → pass

Scope violations:
  none
